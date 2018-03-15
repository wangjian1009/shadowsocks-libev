/*
 * server.c - Provide shadowsocks service
 *
 * Copyright (C) 2013 - 2018, Max Lv <max.c.lv@gmail.com>
 *
 * This file is part of the shadowsocks-libev.
 *
 * shadowsocks-libev is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * shadowsocks-libev is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with shadowsocks-libev; see the file COPYING. If not, see
 * <http://www.gnu.org/licenses/>.
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>
#include <fcntl.h>
#include <locale.h>
#include <signal.h>
#include <string.h>
#include <strings.h>
#include <time.h>
#include <unistd.h>
#include <getopt.h>
#include <math.h>
#ifndef __MINGW32__
#include <netdb.h>
#include <errno.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <pthread.h>
#include <sys/un.h>
#endif
#include <libcork/core.h>

#if defined(HAVE_SYS_IOCTL_H) && defined(HAVE_NET_IF_H) && defined(__linux__)
#include <net/if.h>
#include <sys/ioctl.h>
#define SET_INTERFACE
#endif

#include "netutils.h"
#include "utils.h"
#include "acl.h"
#include "plugin.h"
#include "server.h"
#include "winsock.h"

#ifndef EAGAIN
#define EAGAIN EWOULDBLOCK
#endif

#ifndef EWOULDBLOCK
#define EWOULDBLOCK EAGAIN
#endif

#ifndef BUF_SIZE
#define BUF_SIZE 2048
#endif

#ifndef SSMAXCONN
#define SSMAXCONN 1024
#endif

#ifndef MAX_FRAG
#define MAX_FRAG 1
#endif

#ifdef USE_NFCONNTRACK_TOS

#ifndef MARK_MAX_PACKET
#define MARK_MAX_PACKET 10
#endif

#ifndef MARK_MASK_PREFIX
#define MARK_MASK_PREFIX 0xDC00
#endif

#endif

static void signal_cb(EV_P_ ev_signal *w, int revents);
static void accept_cb(EV_P_ ev_io *w, int revents);
static void server_send_cb(EV_P_ ev_io *w, int revents);
static void server_recv_cb(EV_P_ ev_io *w, int revents);
static void remote_recv_cb(EV_P_ ev_io *w, int revents);
static void remote_send_cb(EV_P_ ev_io *w, int revents);
static void server_timeout_cb(EV_P_ ev_timer *watcher, int revents);
static void block_list_clear_cb(EV_P_ ev_timer *watcher, int revents);

static remote_t *new_remote(int fd);
static server_t *new_server(int fd_or_conv, listen_ctx_t *listener);
static remote_t *connect_to_remote(EV_P_ struct addrinfo *res,
                                   server_t *server);

static void free_remote(remote_t *remote);
static void close_and_free_remote(EV_P_ remote_t *remote);
static void free_server(server_t *server);
static void close_and_free_server(EV_P_ server_t *server);
static void resolv_cb(struct sockaddr *addr, void *data);
static void resolv_free_cb(void *data);

/*Loki: kcp */
static int kcp_output(const char *buf, int len, ikcpcb *kcp, void *user);
static void kcp_update_cb(EV_P_ ev_timer *watcher, int revents);
static void kcp_timer_reset(EV_P_ server_t *server);
static void kcp_forward_data(server_t  * server);
static server_t * kcp_find_server(int conv);
/**/

#define IO_START(__h, __msg, args...)           \
    do {                                        \
        if (verbose && !ev_is_active(&__h)) {   \
            LOGI(__msg, ##args );               \
        }                                       \
        ev_io_start(EV_A_ & __h);               \
    } while(0)

#define IO_STOP(__h, __msg, args...)            \
    do {                                        \
        if (verbose && ev_is_active(&__h)) {    \
            LOGI(__msg, ##args );               \
        }                                       \
        ev_io_stop(EV_A_ & __h);                \
    } while(0)

#define TIMER_START(__h, __msg, args...)                    \
    do {                                                    \
        if (verbose && (__msg)[0] && !ev_is_active(&__h)) { \
            LOGI(__msg, ##args );                           \
        }                                                   \
        ev_timer_start(EV_A_ & __h);                        \
    } while(0)

#define TIMER_STOP(__h, __msg, args...)                     \
    do {                                                    \
        if (verbose && (__msg)[0] && ev_is_active(&__h)) {  \
            LOGI(__msg, ##args );                           \
        }                                                   \
        ev_timer_stop(EV_A_ & __h);                         \
    } while(0)

/**/

int verbose      = 0;
int reuse_port   = 0;
char *local_addr = NULL;

static crypto_t *crypto;

static int acl       = 0;
static int mode      = TCP_ONLY;
static int ipv6first = 0;
static int fast_open = 0;
static int no_delay  = 0;

#ifdef HAVE_SETRLIMIT
static int nofile = 0;
#endif
static int remote_conn = 0;
static int server_conn = 0;

static char *plugin       = NULL;
static char *remote_port  = NULL;
static char *manager_addr = NULL;
uint64_t tx               = 0;
uint64_t rx               = 0;

#ifndef __MINGW32__
ev_timer stat_update_watcher;
#endif
ev_timer block_list_watcher;

static struct ev_signal sigint_watcher;
static struct ev_signal sigterm_watcher;
#ifndef __MINGW32__
static struct ev_signal sigchld_watcher;
#endif

static struct cork_dllist connections;

#ifndef __MINGW32__
static void
stat_update_cb(EV_P_ ev_timer *watcher, int revents)
{
    struct sockaddr_un svaddr, claddr;
    int sfd = -1;
    size_t msgLen;
    char resp[BUF_SIZE];

    if (verbose) {
        LOGI("update traffic stat: tx: %" PRIu64 " rx: %" PRIu64 "", tx, rx);
    }

    snprintf(resp, BUF_SIZE, "stat: {\"%s\":%" PRIu64 "}", remote_port, tx + rx);
    msgLen = strlen(resp) + 1;

    ss_addr_t ip_addr = { .host = NULL, .port = NULL };
    parse_addr(manager_addr, &ip_addr);

    if (ip_addr.host == NULL || ip_addr.port == NULL) {
        sfd = socket(AF_UNIX, SOCK_DGRAM, 0);
        if (sfd == -1) {
            ERROR("stat_socket");
            return;
        }

        memset(&claddr, 0, sizeof(struct sockaddr_un));
        claddr.sun_family = AF_UNIX;
        snprintf(claddr.sun_path, sizeof(claddr.sun_path), "/tmp/shadowsocks.%s", remote_port);

        unlink(claddr.sun_path);

        if (bind(sfd, (struct sockaddr *)&claddr, sizeof(struct sockaddr_un)) == -1) {
            ERROR("stat_bind");
            close(sfd);
            return;
        }

        memset(&svaddr, 0, sizeof(struct sockaddr_un));
        svaddr.sun_family = AF_UNIX;
        strncpy(svaddr.sun_path, manager_addr, sizeof(svaddr.sun_path) - 1);

        if (sendto(sfd, resp, strlen(resp) + 1, 0, (struct sockaddr *)&svaddr,
                   sizeof(struct sockaddr_un)) != msgLen) {
            ERROR("stat_sendto");
            close(sfd);
            return;
        }

        unlink(claddr.sun_path);
    } else {
        struct sockaddr_storage storage;
        memset(&storage, 0, sizeof(struct sockaddr_storage));
        if (get_sockaddr(ip_addr.host, ip_addr.port, &storage, 0, ipv6first) == -1) {
            ERROR("failed to parse the manager addr");
            return;
        }

        sfd = socket(storage.ss_family, SOCK_DGRAM, 0);

        if (sfd == -1) {
            ERROR("stat_socket");
            return;
        }

        size_t addr_len = get_sockaddr_len((struct sockaddr *)&storage);
        if (sendto(sfd, resp, strlen(resp) + 1, 0, (struct sockaddr *)&storage,
                   addr_len) != msgLen) {
            ERROR("stat_sendto");
            close(sfd);
            return;
        }
    }

    close(sfd);
}
#endif

static void
free_connections(struct ev_loop *loop)
{
    struct cork_dllist_item *curr, *next;
    cork_dllist_foreach_void(&connections, curr, next) {
        server_t *server = cork_container_of(curr, server_t, entries);
        remote_t *remote = server->remote;
        close_and_free_server(loop, server);
        close_and_free_remote(loop, remote);
    }
}

static char *
get_peer_name(int fd)
{
    static char peer_name[INET6_ADDRSTRLEN] = { 0 };
    struct sockaddr_storage addr;
    socklen_t len = sizeof(struct sockaddr_storage);
    memset(&addr, 0, len);
    memset(peer_name, 0, INET6_ADDRSTRLEN);
    int err = getpeername(fd, (struct sockaddr *)&addr, &len);
    if (err == 0) {
        if (addr.ss_family == AF_INET) {
            struct sockaddr_in *s = (struct sockaddr_in *)&addr;
            inet_ntop(AF_INET, &s->sin_addr, peer_name, INET_ADDRSTRLEN);
        } else if (addr.ss_family == AF_INET6) {
            struct sockaddr_in6 *s = (struct sockaddr_in6 *)&addr;
            inet_ntop(AF_INET6, &s->sin6_addr, peer_name, INET6_ADDRSTRLEN);
        }
    } else {
        return NULL;
    }
    return peer_name;
}

#ifdef __linux__
static void
set_linger(int fd)
{
    struct linger so_linger;
    memset(&so_linger, 0, sizeof(struct linger));
    so_linger.l_onoff  = 1;
    so_linger.l_linger = 0;
    setsockopt(fd, SOL_SOCKET, SO_LINGER, &so_linger, sizeof so_linger);
}

#endif

static void
reset_addr(int fd)
{
    char *peer_name;
    peer_name = get_peer_name(fd);
    if (peer_name != NULL) {
        remove_from_block_list(peer_name);
    }
}

static void
report_addr(int fd, int err_level, const char *info)
{
#ifdef __linux__
    set_linger(fd);
#endif

    char *peer_name;
    peer_name = get_peer_name(fd);
    if (peer_name != NULL) {
        LOGE("failed to handshake with %s: %s", peer_name, info);
        // Avoid block local plugins
        if (strcmp(peer_name, "127.0.0.1") != 0)
            update_block_list(peer_name, err_level);
    }
}

int
setfastopen(int fd)
{
    int s = 0;
#ifdef TCP_FASTOPEN
    if (fast_open) {
#if defined(__APPLE__) || defined(__MINGW32__)
        int opt = 1;
#else
        int opt = 5;
#endif
        s = setsockopt(fd, IPPROTO_TCP, TCP_FASTOPEN, &opt, sizeof(opt));

        if (s == -1) {
            if (errno == EPROTONOSUPPORT || errno == ENOPROTOOPT) {
                LOGE("fast open is not supported on this platform");
                fast_open = 0;
            } else {
                ERROR("setsockopt");
            }
        }
    }
#endif
    return s;
}

#ifndef __MINGW32__
int
setnonblocking(int fd)
{
    int flags;
    if (-1 == (flags = fcntl(fd, F_GETFL, 0))) {
        flags = 0;
    }
    return fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}
#endif

int
create_and_bind(int socktype, const char *host, const char *port, int mptcp)
{
    struct addrinfo hints;
    struct addrinfo *result, *rp, *ipv4v6bindall;
    int s, listen_sock;

    memset(&hints, 0, sizeof(struct addrinfo));
    hints.ai_family   = AF_UNSPEC;               /* Return IPv4 and IPv6 choices */
    hints.ai_socktype = socktype;             /* We want a TCP socket */
    hints.ai_flags    = AI_PASSIVE | AI_ADDRCONFIG; /* For wildcard IP address */
    hints.ai_protocol = IPPROTO_TCP;

    result = NULL;

    for (int i = 1; i < 8; i++) {
        s = getaddrinfo(host, port, &hints, &result);
        if (s == 0) {
            break;
        } else {
            sleep(pow(2, i));
            LOGE("failed to resolve server name, wait %.0f seconds", pow(2, i));
        }
    }

    if (s != 0) {
        LOGE("getaddrinfo: %s", gai_strerror(s));
        return -1;
    }

    if (result == NULL) {
        LOGE("Could not bind");
        return -1;
    }

    rp = result;

    /*
     * On Linux, with net.ipv6.bindv6only = 0 (the default), getaddrinfo(NULL) with
     * AI_PASSIVE returns 0.0.0.0 and :: (in this order). AI_PASSIVE was meant to
     * return a list of addresses to listen on, but it is impossible to listen on
     * 0.0.0.0 and :: at the same time, if :: implies dualstack mode.
     */
    if (!host) {
        ipv4v6bindall = result;

        /* Loop over all address infos found until a IPV6 address is found. */
        while (ipv4v6bindall) {
            if (ipv4v6bindall->ai_family == AF_INET6) {
                rp = ipv4v6bindall; /* Take first IPV6 address available */
                break;
            }
            ipv4v6bindall = ipv4v6bindall->ai_next; /* Get next address info, if any */
        }
    }

    for (/*rp = result*/; rp != NULL; rp = rp->ai_next) {
        listen_sock = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
        if (listen_sock == -1) {
            continue;
        }

        if (rp->ai_family == AF_INET6) {
            int ipv6only = host ? 1 : 0;
            setsockopt(listen_sock, IPPROTO_IPV6, IPV6_V6ONLY, &ipv6only, sizeof(ipv6only));
        }

        int opt = 1;
        setsockopt(listen_sock, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
#ifdef SO_NOSIGPIPE
        setsockopt(listen_sock, SOL_SOCKET, SO_NOSIGPIPE, &opt, sizeof(opt));
#endif
        if (reuse_port) {
            int err = set_reuseport(listen_sock);
            if (err == 0) {
                LOGI("tcp port reuse enabled");
            }
        }

        if (mptcp == 1 && socktype == SOCK_STREAM) {
            int i = 0;
            while ((mptcp = mptcp_enabled_values[i]) > 0) {
                int err = setsockopt(listen_sock, IPPROTO_TCP, mptcp, &opt, sizeof(opt));
                if (err != -1) {
                    break;
                }
                i++;
            }
            if (mptcp == 0) {
                ERROR("failed to enable multipath TCP");
            }
        }

        s = bind(listen_sock, rp->ai_addr, rp->ai_addrlen);
        if (s == 0) {
            /* We managed to bind successfully! */
            break;
        } else {
            ERROR("bind");
        }

        close(listen_sock);
        listen_sock = -1;
    }

    freeaddrinfo(result);

    return listen_sock;
}

static remote_t *
connect_to_remote(EV_P_ struct addrinfo *res,
                  server_t *server)
{
    int sockfd;
#ifdef SET_INTERFACE
    const char *iface = server->listen_ctx->iface;
#endif

    if (acl) {
        char ipstr[INET6_ADDRSTRLEN];
        memset(ipstr, 0, INET6_ADDRSTRLEN);

        if (res->ai_addr->sa_family == AF_INET) {
            struct sockaddr_in *s = (struct sockaddr_in *)res->ai_addr;
            inet_ntop(AF_INET, &s->sin_addr, ipstr, INET_ADDRSTRLEN);
        } else if (res->ai_addr->sa_family == AF_INET6) {
            struct sockaddr_in6 *s = (struct sockaddr_in6 *)res->ai_addr;
            inet_ntop(AF_INET6, &s->sin6_addr, ipstr, INET6_ADDRSTRLEN);
        }

        if (outbound_block_match_host(ipstr) == 1) {
            if (verbose)
                LOGI("outbound blocked %s", ipstr);
            return NULL;
        }
    }

    // initialize remote socks
    sockfd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (sockfd == -1) {
        ERROR("socket");
        close(sockfd);
        return NULL;
    }

    int opt = 1;
    setsockopt(sockfd, SOL_TCP, TCP_NODELAY, &opt, sizeof(opt));
#ifdef SO_NOSIGPIPE
    setsockopt(sockfd, SOL_SOCKET, SO_NOSIGPIPE, &opt, sizeof(opt));
#endif
    setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));

    // setup remote socks

    if (setnonblocking(sockfd) == -1)
        ERROR("setnonblocking");

    if (local_addr != NULL)
        if (bind_to_address(sockfd, local_addr) == -1) {
            ERROR("bind_to_address");
            close(sockfd);
            return NULL;
        }

#ifdef SET_INTERFACE
    if (iface) {
        if (setinterface(sockfd, iface) == -1) {
            ERROR("setinterface");
            close(sockfd);
            return NULL;
        }
    }
#endif

    remote_t *remote = new_remote(sockfd);

    if (fast_open) {
#if defined(MSG_FASTOPEN) && !defined(TCP_FASTOPEN_CONNECT)
        int s = -1;
        s = sendto(sockfd, server->buf->data, server->buf->len,
                MSG_FASTOPEN, res->ai_addr, res->ai_addrlen);
#elif defined(TCP_FASTOPEN_WINSOCK)
        DWORD s = -1;
        DWORD err = 0;
        do {
            int optval = 1;
            // Set fast open option
            if (setsockopt(sockfd, IPPROTO_TCP, TCP_FASTOPEN,
                           &optval, sizeof(optval)) != 0) {
                ERROR("setsockopt");
                break;
            }
            // Load ConnectEx function
            LPFN_CONNECTEX ConnectEx = winsock_getconnectex();
            if (ConnectEx == NULL) {
                LOGE("Cannot load ConnectEx() function");
                err = WSAENOPROTOOPT;
                break;
            }
            // ConnectEx requires a bound socket
            if (winsock_dummybind(sockfd, res->ai_addr) != 0) {
                ERROR("bind");
                break;
            }
            // Call ConnectEx to send data
            memset(&remote->olap, 0, sizeof(remote->olap));
            remote->connect_ex_done = 0;
            if (ConnectEx(sockfd, res->ai_addr, res->ai_addrlen,
                          server->buf->data, server->buf->len,
                          &s, &remote->olap)) {
                remote->connect_ex_done = 1;
                break;
            };
            // XXX: ConnectEx pending, check later in remote_send
            if (WSAGetLastError() == ERROR_IO_PENDING) {
                err = CONNECT_IN_PROGRESS;
                break;
            }
            ERROR("ConnectEx");
        } while(0);
        // Set error number
        if (err) {
            SetLastError(err);
        }
#else
        int s = -1;
#if defined(TCP_FASTOPEN_CONNECT)
        int optval = 1;
        if(setsockopt(sockfd, IPPROTO_TCP, TCP_FASTOPEN_CONNECT,
                    (void *)&optval, sizeof(optval)) < 0)
            FATAL("failed to set TCP_FASTOPEN_CONNECT");
        s = connect(sockfd, res->ai_addr, res->ai_addrlen);
#elif defined(CONNECT_DATA_IDEMPOTENT)
        ((struct sockaddr_in *)(res->ai_addr))->sin_len = sizeof(struct sockaddr_in);
        sa_endpoints_t endpoints;
        memset((char *)&endpoints, 0, sizeof(endpoints));
        endpoints.sae_dstaddr    = res->ai_addr;
        endpoints.sae_dstaddrlen = res->ai_addrlen;

        s = connectx(sockfd, &endpoints, SAE_ASSOCID_ANY, CONNECT_DATA_IDEMPOTENT,
                         NULL, 0, NULL, NULL);
#else
        FATAL("fast open is not enabled in this build");
#endif
        if (s == 0)
            s = send(sockfd, server->buf->data, server->buf->len, 0);
#endif
        if (s == -1) {
            if (errno == CONNECT_IN_PROGRESS) {
                // The remote server doesn't support tfo or it's the first connection to the server.
                // It will automatically fall back to conventional TCP.
            } else if (errno == EOPNOTSUPP || errno == EPROTONOSUPPORT ||
                       errno == ENOPROTOOPT) {
                // Disable fast open as it's not supported
                fast_open = 0;
                LOGE("fast open is not supported on this platform");
            } else {
                ERROR("fast_open_connect");
            }
        } else {
            server->buf->idx += s;
            server->buf->len -= s;
        }
    }

    if (!fast_open) {
        int r = connect(sockfd, res->ai_addr, res->ai_addrlen);

        if (r == -1 && errno != CONNECT_IN_PROGRESS) {
            ERROR("connect");
            close_and_free_remote(EV_A_ remote);
            return NULL;
        }
    }

    return remote;
}

#ifdef USE_NFCONNTRACK_TOS
int
setMarkDscpCallback(enum nf_conntrack_msg_type type, struct nf_conntrack *ct, void *data)
{
    server_t *server            = (server_t *)data;
    struct dscptracker *tracker = server->tracker;

    tracker->mark = nfct_get_attr_u32(ct, ATTR_MARK);
    if ((tracker->mark & 0xff00) == MARK_MASK_PREFIX) {
        // Extract DSCP value from mark value
        tracker->dscp = tracker->mark & 0x00ff;
        int tos = (tracker->dscp) << 2;
        if (setsockopt(server->fd, IPPROTO_IP, IP_TOS, &tos, sizeof(tos)) != 0) {
            ERROR("iptable setsockopt IP_TOS");
        }
    }
    return NFCT_CB_CONTINUE;
}

void
conntrackQuery(server_t *server)
{
    struct dscptracker *tracker = server->tracker;
    if (tracker && tracker->ct) {
        // Trying query mark from nf conntrack
        struct nfct_handle *h = nfct_open(CONNTRACK, 0);
        if (h) {
            nfct_callback_register(h, NFCT_T_ALL, setMarkDscpCallback, (void *)server);
            int x = nfct_query(h, NFCT_Q_GET, tracker->ct);
            if (x == -1) {
                LOGE("QOS: Failed to retrieve connection mark %s", strerror(errno));
            }
            nfct_close(h);
        } else {
            LOGE("QOS: Failed to open conntrack handle for upstream netfilter mark retrieval.");
        }
    }
}

void
setTosFromConnmark(remote_t *remote, server_t *server)
{
    if (server->tracker && server->tracker->ct) {
        if (server->tracker->mark == 0 && server->tracker->packet_count < MARK_MAX_PACKET) {
            server->tracker->packet_count++;
            conntrackQuery(server);
        }
    } else {
        socklen_t len;
        struct sockaddr_storage sin;
        len = sizeof(sin);
        if (getsockname(remote->fd, (struct sockaddr *)&sin, &len) == 0) {
            struct sockaddr_storage from_addr;
            len = sizeof from_addr;
            if (getpeername(remote->fd, (struct sockaddr *)&from_addr, &len) == 0) {
                if ((server->tracker = (struct dscptracker *)ss_malloc(sizeof(struct dscptracker)))) {
                    if ((server->tracker->ct = nfct_new())) {
                        // Build conntrack query SELECT
                        if (from_addr.ss_family == AF_INET) {
                            struct sockaddr_in *src = (struct sockaddr_in *)&from_addr;
                            struct sockaddr_in *dst = (struct sockaddr_in *)&sin;

                            nfct_set_attr_u8(server->tracker->ct, ATTR_L3PROTO, AF_INET);
                            nfct_set_attr_u32(server->tracker->ct, ATTR_IPV4_DST, dst->sin_addr.s_addr);
                            nfct_set_attr_u32(server->tracker->ct, ATTR_IPV4_SRC, src->sin_addr.s_addr);
                            nfct_set_attr_u16(server->tracker->ct, ATTR_PORT_DST, dst->sin_port);
                            nfct_set_attr_u16(server->tracker->ct, ATTR_PORT_SRC, src->sin_port);
                        } else if (from_addr.ss_family == AF_INET6) {
                            struct sockaddr_in6 *src = (struct sockaddr_in6 *)&from_addr;
                            struct sockaddr_in6 *dst = (struct sockaddr_in6 *)&sin;

                            nfct_set_attr_u8(server->tracker->ct, ATTR_L3PROTO, AF_INET6);
                            nfct_set_attr(server->tracker->ct, ATTR_IPV6_DST, dst->sin6_addr.s6_addr);
                            nfct_set_attr(server->tracker->ct, ATTR_IPV6_SRC, src->sin6_addr.s6_addr);
                            nfct_set_attr_u16(server->tracker->ct, ATTR_PORT_DST, dst->sin6_port);
                            nfct_set_attr_u16(server->tracker->ct, ATTR_PORT_SRC, src->sin6_port);
                        }
                        nfct_set_attr_u8(server->tracker->ct, ATTR_L4PROTO, IPPROTO_TCP);
                        conntrackQuery(server);
                    } else {
                        LOGE("Failed to allocate new conntrack for upstream netfilter mark retrieval.");
                        server->tracker->ct = NULL;
                    }
                }
            }
        }
    }
}

#endif

static void
server_recv_cb(EV_P_ ev_io *w, int revents)
{
    server_t *server              = ((server_ctx_t *)w)->server;
    remote_t *remote              = NULL;

    assert(! server->kcp);
    
    buffer_t *buf = server->buf;

    if (server->stage == STAGE_STREAM) {
        remote = server->remote;
        buf    = remote->buf;

        ev_timer_again(EV_A_ & server->recv_ctx->watcher);
    }

    assert(!server->kcp);
    ssize_t r = recv(server->fd_or_conv, buf->data, BUF_SIZE, 0);

    if (r == 0) {
        // connection closed
        if (verbose) {
            LOGI("server_recv close the connection");
        }
        close_and_free_remote(EV_A_ remote);
        close_and_free_server(EV_A_ server);
        return;
    } else if (r == -1) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            // no data
            // continue to wait for recv
            return;
        } else {
            ERROR("server recv");
            close_and_free_remote(EV_A_ remote);
            close_and_free_server(EV_A_ server);
            return;
        }
    }

    tx      += r;
    buf->len = r;

    int err = crypto->decrypt(buf, server->d_ctx, BUF_SIZE);

    if (err == CRYPTO_ERROR) {
        assert(!server->kcp);
        report_addr(server->fd_or_conv, MALICIOUS, "authentication error");
        close_and_free_remote(EV_A_ remote);
        close_and_free_server(EV_A_ server);
        return;
    } else if (err == CRYPTO_NEED_MORE) {
        if (server->stage != STAGE_STREAM && server->frag > MAX_FRAG) {
            assert(!server->kcp);
            report_addr(server->fd_or_conv, MALICIOUS, "malicious fragmentation");
            close_and_free_remote(EV_A_ remote);
            close_and_free_server(EV_A_ server);
            return;
        }
        server->frag++;
        return;
    }

    // handshake and transmit data
    if (server->stage == STAGE_STREAM) {
        int s = send(remote->fd, remote->buf->data, remote->buf->len, 0);
        if (s == -1) {
            if (errno == EAGAIN || errno == EWOULDBLOCK) {
                // no data, wait for send
                remote->buf->idx = 0;
                IO_STOP(
                    server->recv_ctx->io,
                    "listener[%d]: server[%d]: tcp [- >>>] | send would block",
                    server->listen_ctx->fd, server->fd_or_conv);
                IO_START(
                    remote->send_ctx->io,
                    "listener[%d]: server[%d]: remote [+ >>>] | send would block",
                    server->listen_ctx->fd, server->fd_or_conv);
            } else {
                ERROR("server_recv_send");
                close_and_free_remote(EV_A_ remote);
                close_and_free_server(EV_A_ server);
            }
        } else if (s < remote->buf->len) {
            remote->buf->len -= s;
            remote->buf->idx  = s;
            IO_STOP(
                server->recv_ctx->io,
                "listener[%d]: server[%d]: tcp [- >>>] | send in process",
                server->listen_ctx->fd, server->fd_or_conv);
            IO_START(
                remote->send_ctx->io,
                "listener[%d]: server[%d]: remote [+ >>>] | send in process",
                server->listen_ctx->fd, server->fd_or_conv);
        }
        return;
    } else if (server->stage == STAGE_INIT) {
        /*
         * Shadowsocks TCP Relay Header:
         *
         *    +------+----------+----------+
         *    | ATYP | DST.ADDR | DST.PORT |
         *    +------+----------+----------+
         *    |  1   | Variable |    2     |
         *    +------+----------+----------+
         *
         */

        int offset     = 0;
        int need_query = 0;
        char atyp      = server->buf->data[offset++];
        char host[257] = { 0 };
        uint16_t port  = 0;
        struct addrinfo info;
        struct sockaddr_storage storage;
        memset(&info, 0, sizeof(struct addrinfo));
        memset(&storage, 0, sizeof(struct sockaddr_storage));

        // get remote addr and port
        if ((atyp & ADDRTYPE_MASK) == 1) {
            // IP V4
            struct sockaddr_in *addr = (struct sockaddr_in *)&storage;
            size_t in_addr_len       = sizeof(struct in_addr);
            addr->sin_family = AF_INET;
            if (server->buf->len >= in_addr_len + 3) {
                addr->sin_addr = *(struct in_addr *)(server->buf->data + offset);
                inet_ntop(AF_INET, (const void *)(server->buf->data + offset),
                          host, INET_ADDRSTRLEN);
                offset += in_addr_len;
            } else {
                assert(!server->kcp);
                report_addr(server->fd_or_conv, MALFORMED, "invalid length for ipv4 address");
                close_and_free_server(EV_A_ server);
                return;
            }
            addr->sin_port   = *(uint16_t *)(server->buf->data + offset);
            info.ai_family   = AF_INET;
            info.ai_socktype = SOCK_STREAM;
            info.ai_protocol = IPPROTO_TCP;
            info.ai_addrlen  = sizeof(struct sockaddr_in);
            info.ai_addr     = (struct sockaddr *)addr;
        } else if ((atyp & ADDRTYPE_MASK) == 3) {
            // Domain name
            uint8_t name_len = *(uint8_t *)(server->buf->data + offset);
            if (name_len + 4 <= server->buf->len) {
                memcpy(host, server->buf->data + offset + 1, name_len);
                offset += name_len + 1;
            } else {
                assert(!server->kcp);
                report_addr(server->fd_or_conv, MALFORMED, "invalid host name length");
                close_and_free_server(EV_A_ server);
                return;
            }
            if (acl && outbound_block_match_host(host) == 1) {
                if (verbose)
                    LOGI("outbound blocked %s", host);
                close_and_free_server(EV_A_ server);
                return;
            }
            struct cork_ip ip;
            if (cork_ip_init(&ip, host) != -1) {
                info.ai_socktype = SOCK_STREAM;
                info.ai_protocol = IPPROTO_TCP;
                if (ip.version == 4) {
                    struct sockaddr_in *addr = (struct sockaddr_in *)&storage;
                    inet_pton(AF_INET, host, &(addr->sin_addr));
                    addr->sin_port   = *(uint16_t *)(server->buf->data + offset);
                    addr->sin_family = AF_INET;
                    info.ai_family   = AF_INET;
                    info.ai_addrlen  = sizeof(struct sockaddr_in);
                    info.ai_addr     = (struct sockaddr *)addr;
                } else if (ip.version == 6) {
                    struct sockaddr_in6 *addr = (struct sockaddr_in6 *)&storage;
                    inet_pton(AF_INET6, host, &(addr->sin6_addr));
                    addr->sin6_port   = *(uint16_t *)(server->buf->data + offset);
                    addr->sin6_family = AF_INET6;
                    info.ai_family    = AF_INET6;
                    info.ai_addrlen   = sizeof(struct sockaddr_in6);
                    info.ai_addr      = (struct sockaddr *)addr;
                }
            } else {
                if (!validate_hostname(host, name_len)) {
                    assert(!server->kcp);
                    report_addr(server->fd_or_conv, MALFORMED, "invalid host name");
                    close_and_free_server(EV_A_ server);
                    return;
                }
                need_query = 1;
            }
        } else if ((atyp & ADDRTYPE_MASK) == 4) {
            // IP V6
            struct sockaddr_in6 *addr = (struct sockaddr_in6 *)&storage;
            size_t in6_addr_len       = sizeof(struct in6_addr);
            addr->sin6_family = AF_INET6;
            if (server->buf->len >= in6_addr_len + 3) {
                addr->sin6_addr = *(struct in6_addr *)(server->buf->data + offset);
                inet_ntop(AF_INET6, (const void *)(server->buf->data + offset),
                          host, INET6_ADDRSTRLEN);
                offset += in6_addr_len;
            } else {
                LOGE("invalid header with addr type %d", atyp);
                assert(!server->kcp);
                report_addr(server->fd_or_conv, MALFORMED, "invalid length for ipv6 address");
                close_and_free_server(EV_A_ server);
                return;
            }
            addr->sin6_port  = *(uint16_t *)(server->buf->data + offset);
            info.ai_family   = AF_INET6;
            info.ai_socktype = SOCK_STREAM;
            info.ai_protocol = IPPROTO_TCP;
            info.ai_addrlen  = sizeof(struct sockaddr_in6);
            info.ai_addr     = (struct sockaddr *)addr;
        }

        if (offset == 1) {
            assert(!server->kcp);
            report_addr(server->fd_or_conv, MALFORMED, "invalid address type");
            close_and_free_server(EV_A_ server);
            return;
        }

        port = (*(uint16_t *)(server->buf->data + offset));

        offset += 2;

        if (server->buf->len < offset) {
            assert(!server->kcp);
            report_addr(server->fd_or_conv, MALFORMED, "invalid request length");
            close_and_free_server(EV_A_ server);
            return;
        } else {
            server->buf->len -= offset;
            memmove(server->buf->data, server->buf->data + offset, server->buf->len);
        }

        if (verbose) {
            if ((atyp & ADDRTYPE_MASK) == 4)
                LOGI("connect to [%s]:%d", host, ntohs(port));
            else
                LOGI("connect to %s:%d", host, ntohs(port));
        }

        if (!need_query) {
            remote_t *remote = connect_to_remote(EV_A_ & info, server);

            if (remote == NULL) {
                LOGE("connect error");
                close_and_free_server(EV_A_ server);
                return;
            } else {
                server->remote = remote;
                remote->server = server;

                // XXX: should handle buffer carefully
                if (server->buf->len > 0) {
                    brealloc(remote->buf, server->buf->len, BUF_SIZE);
                    memcpy(remote->buf->data, server->buf->data + server->buf->idx,
                           server->buf->len);
                    remote->buf->len = server->buf->len;
                    remote->buf->idx = 0;
                    server->buf->len = 0;
                    server->buf->idx = 0;
                }

                // waiting on remote connected event
                if (!server->kcp) {
                    IO_STOP(
                        server->recv_ctx->io,
                        "listener[%d]: server[%d]: tcp [- >>>] | connect begin",
                        server->listen_ctx->fd, server->fd_or_conv);
                }
                
                IO_START(
                    remote->send_ctx->io,
                    "listener[%d]: server[%d]: remote [+ >>>] | connect begin",
                    server->listen_ctx->fd, server->fd_or_conv);
            }
        } else {
            IO_STOP(
                server->recv_ctx->io,
                "listener[%d]: server[%d]: %s [- >>>] | resolve hostname begin",
                server->listen_ctx->fd, server->fd_or_conv, server->kcp ? "udp" : "tcp");

            query_t *query = ss_malloc(sizeof(query_t));
            memset(query, 0, sizeof(query_t));
            query->server = server;
            server->query = query;
            snprintf(query->hostname, 256, "%s", host);

            server->stage = STAGE_RESOLVE;
            resolv_start(host, port, resolv_cb, resolv_free_cb, query);
        }

        return;
    }
    // should not reach here
    FATAL("server context error");
}

static void
server_send_cb(EV_P_ ev_io *w, int revents)
{
    server_t *server              = ((server_ctx_t *)w)->server;
    remote_t *remote              = server->remote;

    assert(!server->kcp);
    
    if (remote == NULL) {
        LOGE("invalid server");
        close_and_free_server(EV_A_ server);
        return;
    }

    if (server->buf->len == 0) {
        // close and free
        if (verbose) {
            LOGI("server_send close the connection");
        }
        close_and_free_remote(EV_A_ remote);
        close_and_free_server(EV_A_ server);
        return;
    } else {
        // has data to send
        assert(!server->kcp);
        ssize_t s = send(server->fd_or_conv, server->buf->data + server->buf->idx,
                         server->buf->len, 0);
        if (s == -1) {
            if (errno != EAGAIN && errno != EWOULDBLOCK) {
                ERROR("server_send_send");
                close_and_free_remote(EV_A_ remote);
                close_and_free_server(EV_A_ server);
            }
            return;
        } else if (s < server->buf->len) {
            // partly sent, move memory, wait for the next time to send
            server->buf->len -= s;
            server->buf->idx += s;
            return;
        } else {
            // all sent out, wait for reading
            server->buf->len = 0;
            server->buf->idx = 0;

            if (!server->kcp) {
                IO_STOP(
                    server->send_ctx->io,
                    "listener[%d]: server[%d]: tcp [+ <<<] | tcp cend complete",
                    server->listen_ctx->fd, server->fd_or_conv);
            }
            
            if (remote != NULL) {
                IO_START(
                    remote->recv_ctx->io,
                    "listener[%d]: server[%d]: remote [+ <<<] | tcp cend complete",
                    server->listen_ctx->fd, server->fd_or_conv);
                return;
            } else {
                LOGE("invalid remote");
                close_and_free_remote(EV_A_ remote);
                close_and_free_server(EV_A_ server);
                return;
            }
        }
    }
}

static void
block_list_clear_cb(EV_P_ ev_timer *watcher, int revents)
{
    clear_block_list();
}

static void
server_timeout_cb(EV_P_ ev_timer *watcher, int revents)
{
    server_ctx_t *server_ctx
        = cork_container_of(watcher, server_ctx_t, watcher);
    server_t *server = server_ctx->server;
    remote_t *remote = server->remote;

    if (verbose) {
        LOGI("TCP connection timeout");
    }

    close_and_free_remote(EV_A_ remote);
    close_and_free_server(EV_A_ server);
}

static void
resolv_free_cb(void *data)
{
    query_t *query = (query_t *)data;

    if (query != NULL) {
        if (query->server != NULL)
            query->server->query = NULL;
        ss_free(query);
    }
}

static void
resolv_cb(struct sockaddr *addr, void *data)
{
    query_t *query   = (query_t *)data;
    server_t *server = query->server;

    if (server == NULL)
        return;

    struct ev_loop *loop = server->listen_ctx->loop;

    if (addr == NULL) {
        LOGE("unable to resolve %s", query->hostname);
        close_and_free_server(EV_A_ server);
    } else {
        if (verbose) {
            LOGI("successfully resolved %s", query->hostname);
        }

        struct addrinfo info;
        memset(&info, 0, sizeof(struct addrinfo));
        info.ai_socktype = SOCK_STREAM;
        info.ai_protocol = IPPROTO_TCP;
        info.ai_addr     = addr;

        if (addr->sa_family == AF_INET) {
            info.ai_family  = AF_INET;
            info.ai_addrlen = sizeof(struct sockaddr_in);
        } else if (addr->sa_family == AF_INET6) {
            info.ai_family  = AF_INET6;
            info.ai_addrlen = sizeof(struct sockaddr_in6);
        }

        remote_t *remote = connect_to_remote(EV_A_ & info, server);

        if (remote == NULL) {
            close_and_free_server(EV_A_ server);
        } else {
            server->remote = remote;
            remote->server = server;

            // XXX: should handle buffer carefully
            if (server->buf->len > 0) {
                brealloc(remote->buf, server->buf->len, BUF_SIZE);
                memcpy(remote->buf->data, server->buf->data + server->buf->idx,
                       server->buf->len);
                remote->buf->len = server->buf->len;
                remote->buf->idx = 0;
                server->buf->len = 0;
                server->buf->idx = 0;
            }

            // listen to remote connected event
            IO_START(
                remote->send_ctx->io,
                "listener[%d]: server[%d]: remote [+ >>>] | connect begin",
                server->listen_ctx->fd, server->fd_or_conv);
        }
    }
}

static void
remote_recv_cb(EV_P_ ev_io *w, int revents)
{
    remote_t *remote              = ((remote_ctx_t *)w)->remote;
    server_t *server              = remote->server;

    if (server == NULL) {
        LOGE("invalid server");
        close_and_free_remote(EV_A_ remote);
        return;
    }

    ev_timer_again(EV_A_ & server->recv_ctx->watcher);

    ssize_t r = recv(remote->fd, server->buf->data, BUF_SIZE, 0);

    if (r == 0) {
        // connection closed
        if (verbose) {
            LOGI("remote_recv close the connection");
        }
        close_and_free_remote(EV_A_ remote);
        close_and_free_server(EV_A_ server);
        return;
    } else if (r == -1) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            // no data
            // continue to wait for recv
            return;
        } else {
            ERROR("remote recv");
            close_and_free_remote(EV_A_ remote);
            close_and_free_server(EV_A_ server);
            return;
        }
    }

    rx += r;

    server->buf->len = r;
    int err = crypto->encrypt(server->buf, server->e_ctx, BUF_SIZE);

    if (err) {
        LOGE("invalid password or cipher");
        close_and_free_remote(EV_A_ remote);
        close_and_free_server(EV_A_ server);
        return;
    }

#ifdef USE_NFCONNTRACK_TOS
    setTosFromConnmark(remote, server);
#endif
    if (server->kcp) {
        int nret = ikcp_input(server->kcp, server->buf->data, server->buf->len);
        if (nret < 0) {
            if (verbose) {
                LOGE("listen[%d]: server[%d]: kcp     <<< error, rv=%d", server->listen_ctx->fd, server->fd_or_conv, nret);
            }
            ERROR("kcp_input_error");
            close_and_free_remote(EV_A_ remote);
            close_and_free_server(EV_A_ server);
            return;
        }
        if (verbose) {
            LOGI("listen[%d]: server[%d]: kcp     <<< %d", server->listen_ctx->fd, server->fd_or_conv, nret);
        }

        kcp_forward_data(server);
    }
    else {
        int s = send(server->fd_or_conv, server->buf->data, server->buf->len, 0);

        if (s == -1) {
            if (errno == EAGAIN || errno == EWOULDBLOCK) {
                // no data, wait for send
                server->buf->idx = 0;
                IO_STOP(remote->recv_ctx->io,
                    "listener[%d]: server[%d]: remote [- <<<] | remote send would block",
                    server->listen_ctx->fd, server->fd_or_conv);

                assert(!server->kcp);
                IO_START(
                    server->send_ctx->io,
                    "listener[%d]: server[%d]: tcp [+ <<<] | remote send would block",
                    server->listen_ctx->fd, server->fd_or_conv);
            } else {
                ERROR("remote_recv_send");
                close_and_free_remote(EV_A_ remote);
                close_and_free_server(EV_A_ server);
                return;
            }
        } else if (s < server->buf->len) {
            server->buf->len -= s;
            server->buf->idx  = s;

            IO_STOP(
                remote->recv_ctx->io,
                "listener[%d]: server[%d]: remote [- <<<] | tcp send in process",
                server->listen_ctx->fd, server->fd_or_conv);

            assert(!server->kcp);
            IO_START(
                server->send_ctx->io,
                "listener[%d]: server[%d]: tcp [+ <<<] | tcp send in process",
                server->listen_ctx->fd, server->fd_or_conv);
        }
    }

    // Disable TCP_NODELAY after the first response are sent
    if (!remote->recv_ctx->connected && !no_delay) {
        int opt = 0;
        if (!server->kcp) setsockopt(server->fd_or_conv, SOL_TCP, TCP_NODELAY, &opt, sizeof(opt));
        setsockopt(remote->fd, SOL_TCP, TCP_NODELAY, &opt, sizeof(opt));
    }
    remote->recv_ctx->connected = 1;
}

static void
remote_send_cb(EV_P_ ev_io *w, int revents)
{
    remote_t *remote              = ((remote_ctx_t *)w)->remote;
    server_t *server              = remote->server;

    if (server == NULL) {
        LOGE("invalid server");
        close_and_free_remote(EV_A_ remote);
        return;
    }

    if (!remote->send_ctx->connected) {
#ifdef TCP_FASTOPEN_WINSOCK
        if (fast_open) {
            // Check if ConnectEx is done
            if (!remote->connect_ex_done) {
                DWORD numBytes;
                DWORD flags;
                // Non-blocking way to fetch ConnectEx result
                if (WSAGetOverlappedResult(remote->fd, &remote->olap,
                                           &numBytes, FALSE, &flags)) {
                    remote->buf->len -= numBytes;
                    remote->buf->idx  = numBytes;
                    remote->connect_ex_done = 1;
                } else if (WSAGetLastError() == WSA_IO_INCOMPLETE) {
                    // XXX: ConnectEx still not connected, wait for next time
                    return;
                } else {
                    ERROR("WSAGetOverlappedResult");
                    // not connected
                    close_and_free_remote(EV_A_ remote);
                    close_and_free_server(EV_A_ server);
                    return;
                };
            }

            // Make getpeername work
            if (setsockopt(remote->fd, SOL_SOCKET,
                           SO_UPDATE_CONNECT_CONTEXT, NULL, 0) != 0) {
                ERROR("setsockopt");
            }
        }
#endif
        struct sockaddr_storage addr;
        socklen_t len = sizeof(struct sockaddr_storage);
        memset(&addr, 0, len);
        int r = getpeername(remote->fd, (struct sockaddr *)&addr, &len);
        if (r == 0) {
            if (verbose) {
                LOGI("remote connected");
            }
            remote->send_ctx->connected = 1;

            // Clear the state of this address in the block list
            assert(!server->kcp);
            reset_addr(server->fd_or_conv);

            if (remote->buf->len == 0) {
                server->stage = STAGE_STREAM;
                IO_STOP(
                    remote->send_ctx->io,
                    "listener[%d]: server[%d]: remote [- >>>] | remote getpeername success",
                    server->listen_ctx->fd, server->fd_or_conv);

                assert(!server->kcp);
                IO_START(
                    server->recv_ctx->io,
                    "listener[%d]: server[%d]: tcp [+ >>>] | remote getpeername success",
                    server->listen_ctx->fd, server->fd_or_conv);

                IO_START(
                    remote->recv_ctx->io,
                    "listener[%d]: server[%d]: remote [+ <<<] | remote getpeername success",
                    server->listen_ctx->fd, server->fd_or_conv);
                return;
            }
        } else {
            ERROR("getpeername");
            // not connected
            close_and_free_remote(EV_A_ remote);
            close_and_free_server(EV_A_ server);
            return;
        }
    }

    if (remote->buf->len == 0) {
        // close and free
        if (verbose) {
            LOGI("remote_send close the connection");
        }
        close_and_free_remote(EV_A_ remote);
        close_and_free_server(EV_A_ server);
        return;
    } else {
        // has data to send
        ssize_t s = send(remote->fd, remote->buf->data + remote->buf->idx,
                         remote->buf->len, 0);
        if (s == -1) {
            if (errno != EAGAIN && errno != EWOULDBLOCK) {
                ERROR("remote_send_send");
                // close and free
                close_and_free_remote(EV_A_ remote);
                close_and_free_server(EV_A_ server);
            }
            return;
        } else if (s < remote->buf->len) {
            // partly sent, move memory, wait for the next time to send
            remote->buf->len -= s;
            remote->buf->idx += s;
            return;
        } else {
            // all sent out, wait for reading
            remote->buf->len = 0;
            remote->buf->idx = 0;

            IO_STOP(
                remote->send_ctx->io,
                "listener[%d]: server[%d]: remote [- >>>] | remote send complete",
                server->listen_ctx->fd, server->fd_or_conv);
            
            if (server != NULL) {
                if (!server->kcp) {
                    IO_START(
                        server->recv_ctx->io,
                        "listener[%d]: server[%d]: tcp [+ >>>] | remote send complete",
                        server->listen_ctx->fd, server->fd_or_conv);
                }
                
                if (server->stage != STAGE_STREAM) {
                    server->stage = STAGE_STREAM;
                    IO_START(
                        remote->recv_ctx->io,
                        "listener[%d]: server[%d]: remote [+ <<<] | remote send complete",
                        server->listen_ctx->fd, server->fd_or_conv);
                }
            } else {
                LOGE("invalid server");
                close_and_free_remote(EV_A_ remote);
                close_and_free_server(EV_A_ server);
            }
            return;
        }
    }
}

static remote_t *
new_remote(int fd)
{
    if (verbose) {
        remote_conn++;
    }

    remote_t *remote = ss_malloc(sizeof(remote_t));
    memset(remote, 0, sizeof(remote_t));

    remote->recv_ctx = ss_malloc(sizeof(remote_ctx_t));
    remote->send_ctx = ss_malloc(sizeof(remote_ctx_t));
    remote->buf      = ss_malloc(sizeof(buffer_t));
    balloc(remote->buf, BUF_SIZE);
    memset(remote->recv_ctx, 0, sizeof(remote_ctx_t));
    memset(remote->send_ctx, 0, sizeof(remote_ctx_t));
    remote->fd                  = fd;
    remote->recv_ctx->remote    = remote;
    remote->recv_ctx->connected = 0;
    remote->send_ctx->remote    = remote;
    remote->send_ctx->connected = 0;
    remote->server              = NULL;

    ev_io_init(&remote->recv_ctx->io, remote_recv_cb, fd, EV_READ);
    ev_io_init(&remote->send_ctx->io, remote_send_cb, fd, EV_WRITE);

    return remote;
}

static void
free_remote(remote_t *remote)
{
    if (remote->server != NULL) {
        remote->server->remote = NULL;
    }
    if (remote->buf != NULL) {
        bfree(remote->buf);
        ss_free(remote->buf);
    }
    ss_free(remote->recv_ctx);
    ss_free(remote->send_ctx);
    ss_free(remote);
}

static void
close_and_free_remote(EV_P_ remote_t *remote)
{
    if (remote != NULL) {
        server_t * server = remote->server;

        IO_STOP(
            remote->send_ctx->io,
            "listener[%d]: server[%d]: remote [- >>>] | remote free",
            server->listen_ctx->fd, server->fd_or_conv);
        
        IO_STOP(
            remote->recv_ctx->io,
            "listener[%d]: server[%d]: remote [- <<<] | remote free",
            server->listen_ctx->fd, server->fd_or_conv);

        close(remote->fd);
        free_remote(remote);
        if (verbose) {
            remote_conn--;
            LOGI("current remote connection: %d", remote_conn);
        }
    }
}

static server_t *
new_server(int fd_or_conv, listen_ctx_t *listener)
{
    if (verbose) {
        server_conn++;
    }

    server_t *server;
    server = ss_malloc(sizeof(server_t));

    memset(server, 0, sizeof(server_t));

    server->recv_ctx = ss_malloc(sizeof(server_ctx_t));
    server->send_ctx = ss_malloc(sizeof(server_ctx_t));
    server->buf      = ss_malloc(sizeof(buffer_t));
    memset(server->recv_ctx, 0, sizeof(server_ctx_t));
    memset(server->send_ctx, 0, sizeof(server_ctx_t));
    balloc(server->buf, BUF_SIZE);
    server->fd_or_conv                  = fd_or_conv;
    server->recv_ctx->server    = server;
    server->send_ctx->server    = server;
    server->stage               = STAGE_INIT;
    server->frag                = 0;
    server->query               = NULL;
    server->listen_ctx          = listener;
    server->remote              = NULL;

    server->e_ctx = ss_align(sizeof(cipher_ctx_t));
    server->d_ctx = ss_align(sizeof(cipher_ctx_t));
    crypto->ctx_init(crypto->cipher, server->e_ctx, 1);
    crypto->ctx_init(crypto->cipher, server->d_ctx, 0);

    /*Loki: init kcmp*/
    if (listener->use_kcp) {
        server->kcp                 = ikcp_create(fd_or_conv, server);
    
        server->kcp->output	= kcp_output;
        /* ikcp_wndsize(server->kcp, param->sndwnd, param->rcvwnd); */
        /* ikcp_nodelay(server->kcp, param->nodelay, param->interval, param->resend, param->nc); */

        server->kcp_watcher.data = server;
        ev_timer_init(&server->kcp_watcher, kcp_update_cb, 0.001, 0.001);
    }
    else {
        server->kcp = NULL;

        ev_io_init(&server->recv_ctx->io, server_recv_cb, fd_or_conv, EV_READ);
        ev_io_init(&server->send_ctx->io, server_send_cb, fd_or_conv, EV_WRITE);
    }
    /**/
    
    int request_timeout = min(MAX_REQUEST_TIMEOUT, listener->timeout) + rand() % MAX_REQUEST_TIMEOUT;
    ev_timer_init(&server->recv_ctx->watcher, server_timeout_cb, request_timeout, listener->timeout);

    cork_dllist_add(&connections, &server->entries);

    return server;
}

static void
free_server(server_t *server)
{
#ifdef USE_NFCONNTRACK_TOS
    if (server->tracker) {
        struct dscptracker *tracker = server->tracker;
        struct nf_conntrack *ct     = server->tracker->ct;
        server->tracker = NULL;
        if (ct) {
            nfct_destroy(ct);
        }
        free(tracker);
    }
#endif
    cork_dllist_remove(&server->entries);

    if (server->remote != NULL) {
        server->remote->server = NULL;
    }
    if (server->e_ctx != NULL) {
        crypto->ctx_release(server->e_ctx);
        ss_free(server->e_ctx);
    }
    if (server->d_ctx != NULL) {
        crypto->ctx_release(server->d_ctx);
        ss_free(server->d_ctx);
    }
    if (server->buf != NULL) {
        bfree(server->buf);
        ss_free(server->buf);
    }

    /*Loki: kcp*/
    if (server->kcp != NULL) {
        ikcp_release(server->kcp);
        server->kcp = NULL;
    }
    
    ss_free(server->recv_ctx);
    ss_free(server->send_ctx);
    ss_free(server);
}

static void
close_and_free_server(EV_P_ server_t *server)
{
    if (server != NULL) {
        if (server->query != NULL) {
            server->query->server = NULL;
            server->query         = NULL;
        }

        IO_STOP(
            server->send_ctx->io,
            "listener[%d]: server[%d]: %s [- <<<] | server free",
            server->listen_ctx->fd, server->fd_or_conv, server->kcp ? "udp" : "tcp");

        IO_STOP(
            server->recv_ctx->io,
            "listener[%d]: server[%d]: %s [- >>>] | server free",
            server->listen_ctx->fd, server->fd_or_conv, server->kcp ? "udp" : "tcp");
            
        ev_timer_stop(EV_A_ & server->recv_ctx->watcher);
        if (!server->kcp) close(server->fd_or_conv);
        free_server(server);
        if (verbose) {
            server_conn--;
            LOGI("current server connection: %d", server_conn);
        }
    }
}

static void
signal_cb(EV_P_ ev_signal *w, int revents)
{
    if (revents & EV_SIGNAL) {
        switch (w->signum) {
#ifndef __MINGW32__
        case SIGCHLD:
            if (!is_plugin_running())
                LOGE("plugin service exit unexpectedly");
            else
                return;
#endif
        case SIGINT:
        case SIGTERM:
            ev_signal_stop(EV_DEFAULT, &sigint_watcher);
            ev_signal_stop(EV_DEFAULT, &sigterm_watcher);
#ifndef __MINGW32__
            ev_signal_stop(EV_DEFAULT, &sigchld_watcher);
#endif
            ev_unloop(EV_A_ EVUNLOOP_ALL);
        }
    }
}

static void
accept_cb(EV_P_ ev_io *w, int revents)
{
    listen_ctx_t *listener = (listen_ctx_t *)w;

    if (listener->use_kcp) {
        struct sockaddr_in clientaddr;
        int clientlen = sizeof(clientaddr);
        memset(&clientaddr, 0, clientlen);
	
        char buf[2048] = {0};
        int len = recvfrom(listener->fd, buf, sizeof(buf) - 1, 0, (struct sockaddr *) &clientaddr, (socklen_t*)&clientlen);
        if (len < 0) {
            LOGE("listener[%d]: udp >>> error | %s", listener->fd, strerror(errno));
            return;
        }	
        
        int conv = ikcp_getconv(buf);

        server_t * server = kcp_find_server(conv);
        if (server == NULL) {
            server = new_server(conv, listener);
            ev_timer_start(EV_A_ & server->recv_ctx->watcher);
        }

		int nret = ikcp_send(server->kcp, buf, len);
		if (nret < 0) {
			LOGE("listener[%d]: server[%d]: kcp     >>> error(%d)", listener->fd, server->fd_or_conv, nret);
            return;
		}

        if (verbose) {
			LOGI("listener[%d]: server[%d]: kcp     >>> %d", listener->fd, server->fd_or_conv, nret);
        }
    }
    else {
        int fd = accept(listener->fd, NULL, NULL);
        if (fd == -1) {
            ERROR("accept");
            return;
        }

        char *peer_name = get_peer_name(fd);
        if (peer_name != NULL) {
            int in_white_list = 0;
            if (acl) {
                if ((get_acl_mode() == BLACK_LIST && acl_match_host(peer_name) == 1)
                    || (get_acl_mode() == WHITE_LIST && acl_match_host(peer_name) >= 0)) {
                    LOGE("Access denied from %s", peer_name);
                    close(fd);
                    return;
                } else if (acl_match_host(peer_name) == -1) {
                    in_white_list = 1;
                }
            }
            if (!in_white_list && plugin == NULL
                && check_block_list(peer_name)) {
                LOGE("block all requests from %s", peer_name);
#ifdef __linux__
                set_linger(fd);
#endif
                close(fd);
                return;
            }
        }

        int opt = 1;
        setsockopt(fd, SOL_TCP, TCP_NODELAY, &opt, sizeof(opt));
#ifdef SO_NOSIGPIPE
        setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &opt, sizeof(opt));
#endif
        setnonblocking(fd);

        if (verbose) {
            LOGI("accept a connection");
        }

        server_t *server = new_server(fd, listener);
        IO_START(
            server->recv_ctx->io,
            "listener[%d]: server[%d]: tcp [+ >>>] | accept success",
            server->listen_ctx->fd, server->fd_or_conv);
        ev_timer_start(EV_A_ & server->recv_ctx->watcher);
    }
}

/*Loki: kcp */
static int kcp_output(const char *buf, int len, ikcpcb *kcp, void *user) {
    server_t * server = user;
	/* int nret = sendto(server->fd, buf, len, 0, (struct sockaddr *)&server->addr, server->addr_len); */
	/* if (nret != 0) { */
    /*     if (verbose) { */
    /*         if (nret != len) { */
    /*             LOGI("server[%d]: udp         >>> %d | %d", server->fd, nret, (len - nret)); */
    /*         } */
    /*         else { */
    /*             LOGI("server[%d]: udp         >>> %d", server->fd, nret); */
    /*         } */
    /*     } */
    /* } */
	/* else { */
    /*     LOGE("server[%d]: udp         >>> %d data error: %s", server->fd, len, strerror(errno)); */
    /* } */

	/* return nret; */
    return 0;
}

static void kcp_update_cb(EV_P_ ev_timer *watcher, int revents) {
    server_t * server = watcher->data;
    struct timeval ptv;
    IUINT32 millisec;

	gettimeofday(&ptv, NULL);

    millisec = (IUINT32)(ptv.tv_usec / 1000) + (IUINT32)ptv.tv_sec * 1000;
    ikcp_update(server->kcp, millisec);
    //LOGI("XXXX: update, len=%d", (int)server->buf->len);

    kcp_timer_reset(EV_A_ server);
}

static void kcp_timer_reset(EV_P_ server_t *server) {
    TIMER_STOP(server->kcp_watcher, "server[%d]: kcp [- update]", server->fd_or_conv);

    if (1) {
        struct timeval ptv;
        gettimeofday(&ptv, NULL);

        IUINT32 current_ms  = (IUINT32)(ptv.tv_usec / 1000) + (IUINT32)ptv.tv_sec * 1000;
        IUINT32 update_ms = ikcp_check(server->kcp, current_ms);

        ev_timer_set(&server->kcp_watcher, (float)(update_ms - current_ms) / 1000.0f, 0);
        TIMER_START(server->kcp_watcher, "");
    }
}

static void kcp_forward_data(server_t  * server)
{
	while(1) {
		char obuf[2046] = {0};
		int nrecv = ikcp_recv(server->kcp, obuf, sizeof(obuf));
		if (nrecv < 0) {
			if (nrecv == -3) {
				LOGE("listener[%d]: server[%d]: kcp recv error, obuf is small, need to extend it", server->listen_ctx->fd, server->fd_or_conv);
            }
			break;
		}

		/* if (task->bev) */
		/* 	evbuffer_add(bufferevent_get_output(task->bev), obuf, nrecv); */
		/* else */
		/* 	debug(LOG_INFO, "this task has finished"); */
	}
}

static server_t * kcp_find_server(int conv) {
    struct cork_dllist_item *curr, *next;
    cork_dllist_foreach_void(&connections, curr, next) {
        server_t * server = cork_container_of(curr, server_t, entries);
        if (server->kcp && server->fd_or_conv == conv) return server;
    }

    return NULL;
}

/**/

int
main(int argc, char **argv)
{
    int i, c;
    int pid_flags   = 0;
    int mptcp       = 0;
    int mtu         = 0;
    uint8_t use_kcp = 0;
    char *user      = NULL;
    char *password  = NULL;
    char *key       = NULL;
    char *timeout   = NULL;
    char *method    = NULL;
    char *pid_path  = NULL;
    char *conf_path = NULL;
    char *iface     = NULL;

    char *server_port = NULL;
    char *plugin_opts = NULL;
    char *plugin_port = NULL;
#ifndef __MINGW32__
    char tmp_port[8];
#endif

    int server_num = 0;
    const char *server_host[MAX_REMOTE_NUM];

    char *nameservers = NULL;

    static struct option long_options[] = {
        { "fast-open",       no_argument,       NULL, GETOPT_VAL_FAST_OPEN   },
        { "reuse-port",      no_argument,       NULL, GETOPT_VAL_REUSE_PORT  },
        { "no-delay",        no_argument,       NULL, GETOPT_VAL_NODELAY     },
        { "acl",             required_argument, NULL, GETOPT_VAL_ACL         },
        { "manager-address", required_argument, NULL,
          GETOPT_VAL_MANAGER_ADDRESS },
        { "mtu",             required_argument, NULL, GETOPT_VAL_MTU         },
        { "help",            no_argument,       NULL, GETOPT_VAL_HELP        },
        { "plugin",          required_argument, NULL, GETOPT_VAL_PLUGIN      },
        { "plugin-opts",     required_argument, NULL, GETOPT_VAL_PLUGIN_OPTS },
        { "password",        required_argument, NULL, GETOPT_VAL_PASSWORD    },
        { "key",             required_argument, NULL, GETOPT_VAL_KEY         },
        { "kcp",             required_argument, NULL, GETOPT_VAL_KCP         },
#ifdef __linux__
        { "mptcp",           no_argument,       NULL, GETOPT_VAL_MPTCP       },
#endif
        { NULL,                              0, NULL,                      0 }
    };

    opterr = 0;

    USE_TTY();

    while ((c = getopt_long(argc, argv, "f:s:p:l:k:t:m:b:c:i:d:a:n:huUv6A",
                            long_options, NULL)) != -1) {
        switch (c) {
        case GETOPT_VAL_FAST_OPEN:
            fast_open = 1;
            break;
        case GETOPT_VAL_NODELAY:
            no_delay = 1;
            LOGI("enable TCP no-delay");
            break;
        case GETOPT_VAL_KCP:
            use_kcp = 1;
            LOGI("enable KCP");
            break;
        case GETOPT_VAL_ACL:
            LOGI("initializing acl...");
            acl = !init_acl(optarg);
            break;
        case GETOPT_VAL_MANAGER_ADDRESS:
            manager_addr = optarg;
            break;
        case GETOPT_VAL_MTU:
            mtu = atoi(optarg);
            LOGI("set MTU to %d", mtu);
            break;
        case GETOPT_VAL_PLUGIN:
            plugin = optarg;
            break;
        case GETOPT_VAL_PLUGIN_OPTS:
            plugin_opts = optarg;
            break;
        case GETOPT_VAL_MPTCP:
            mptcp = 1;
            LOGI("enable multipath TCP");
            break;
        case GETOPT_VAL_KEY:
            key = optarg;
            break;
        case GETOPT_VAL_REUSE_PORT:
            reuse_port = 1;
            break;
        case 's':
            if (server_num < MAX_REMOTE_NUM) {
                server_host[server_num++] = optarg;
            }
            break;
        case 'b':
            local_addr = optarg;
            break;
        case 'p':
            server_port = optarg;
            break;
        case GETOPT_VAL_PASSWORD:
        case 'k':
            password = optarg;
            break;
        case 'f':
            pid_flags = 1;
            pid_path  = optarg;
            break;
        case 't':
            timeout = optarg;
            break;
        case 'm':
            method = optarg;
            break;
        case 'c':
            conf_path = optarg;
            break;
        case 'i':
            iface = optarg;
            break;
        case 'd':
            nameservers = optarg;
            break;
        case 'a':
            user = optarg;
            break;
#ifdef HAVE_SETRLIMIT
        case 'n':
            nofile = atoi(optarg);
            break;
#endif
        case 'u':
            mode = TCP_AND_UDP;
            break;
        case 'U':
            mode = UDP_ONLY;
            break;
        case 'v':
            verbose = 1;
            break;
        case GETOPT_VAL_HELP:
        case 'h':
            usage();
            exit(EXIT_SUCCESS);
        case '6':
            ipv6first = 1;
            break;
        case 'A':
            FATAL("One time auth has been deprecated. Try AEAD ciphers instead.");
            break;
        case '?':
            // The option character is not recognized.
            LOGE("Unrecognized option: %s", optarg);
            opterr = 1;
            break;
        }
    }

    if (opterr) {
        usage();
        exit(EXIT_FAILURE);
    }

    if (argc == 1) {
        if (conf_path == NULL) {
            conf_path = get_default_conf();
        }
    }

    if (conf_path != NULL) {
        jconf_t *conf = read_jconf(conf_path);
        if (server_num == 0) {
            server_num = conf->remote_num;
            for (i = 0; i < server_num; i++)
                server_host[i] = conf->remote_addr[i].host;
        }
        if (server_port == NULL) {
            server_port = conf->remote_port;
        }
        if (password == NULL) {
            password = conf->password;
        }
        if (key == NULL) {
            key = conf->key;
        }
        if (method == NULL) {
            method = conf->method;
        }
        if (timeout == NULL) {
            timeout = conf->timeout;
        }
        if (user == NULL) {
            user = conf->user;
        }
        if (plugin == NULL) {
            plugin = conf->plugin;
        }
        if (plugin_opts == NULL) {
            plugin_opts = conf->plugin_opts;
        }
        if (mode == TCP_ONLY) {
            mode = conf->mode;
        }
        if (mtu == 0) {
            mtu = conf->mtu;
        }
        if (mptcp == 0) {
            mptcp = conf->mptcp;
        }
        if (no_delay == 0) {
            no_delay = conf->no_delay;
        }
        if (reuse_port == 0) {
            reuse_port = conf->reuse_port;
        }
        if (fast_open == 0) {
            fast_open = conf->fast_open;
        }
        if (local_addr == NULL) {
            local_addr = conf->local_addr;
        }
#ifdef HAVE_SETRLIMIT
        if (nofile == 0) {
            nofile = conf->nofile;
        }
#endif
        if (nameservers == NULL) {
            nameservers = conf->nameserver;
        }
        if (ipv6first == 0) {
            ipv6first = conf->ipv6_first;
        }
    }

    if (server_num == 0) {
        server_host[server_num++] = "0.0.0.0";
    }

    if (server_num == 0 || server_port == NULL
        || (password == NULL && key == NULL)) {
        usage();
        exit(EXIT_FAILURE);
    }

    remote_port = server_port;

#ifdef __MINGW32__
    winsock_init();
#endif

    if (plugin != NULL) {
#ifndef __MINGW32__
        uint16_t port = get_local_port();
        if (port == 0) {
            FATAL("failed to find a free port");
        }
        snprintf(tmp_port, 8, "%d", port);
        plugin_port = server_port;
        server_port = tmp_port;
#else
        FATAL("plugins not implemented in MinGW port");
#endif
    }

    if (method == NULL) {
        method = "rc4-md5";
    }

    if (timeout == NULL) {
        timeout = "60";
    }

#ifdef HAVE_SETRLIMIT
    /*
     * no need to check the return value here since we will show
     * the user an error message if setrlimit(2) fails
     */
    if (nofile > 1024) {
        if (verbose) {
            LOGI("setting NOFILE to %d", nofile);
        }
        set_nofile(nofile);
    }
#endif

    USE_SYSLOG(argv[0], pid_flags);
    if (pid_flags) {
        daemonize(pid_path);
    }

    if (ipv6first) {
        LOGI("resolving hostname to IPv6 address first");
    }

    if (fast_open == 1) {
#ifdef TCP_FASTOPEN
        LOGI("using tcp fast open");
#else
        LOGE("tcp fast open is not supported by this environment");
        fast_open = 0;
#endif
    }

    if (plugin != NULL) {
        LOGI("plugin \"%s\" enabled", plugin);
    }

    if (mode != TCP_ONLY) {
        LOGI("UDP relay enabled");
    }

    if (mode == UDP_ONLY) {
        LOGI("TCP relay disabled");
    }

    if (no_delay) {
        LOGI("enable TCP no-delay");
    }

#ifndef __MINGW32__
    // ignore SIGPIPE
    signal(SIGPIPE, SIG_IGN);
    signal(SIGABRT, SIG_IGN);
#endif

    ev_signal_init(&sigint_watcher, signal_cb, SIGINT);
    ev_signal_init(&sigterm_watcher, signal_cb, SIGTERM);
    ev_signal_start(EV_DEFAULT, &sigint_watcher);
    ev_signal_start(EV_DEFAULT, &sigterm_watcher);
#ifndef __MINGW32__
    ev_signal_init(&sigchld_watcher, signal_cb, SIGCHLD);
    ev_signal_start(EV_DEFAULT, &sigchld_watcher);
#endif

    // setup keys
    LOGI("initializing ciphers... %s", method);
    crypto = crypto_init(password, key, method);
    if (crypto == NULL)
        FATAL("failed to initialize ciphers");

    // initialize ev loop
    struct ev_loop *loop = EV_DEFAULT;

    // setup dns
    resolv_init(loop, nameservers, ipv6first);

    if (nameservers != NULL)
        LOGI("using nameserver: %s", nameservers);

#ifndef __MINGW32__
    // Start plugin server
    if (plugin != NULL) {
        int len          = 0;
        size_t buf_size  = 256 * server_num;
        char *server_str = ss_malloc(buf_size);

        snprintf(server_str, buf_size, "%s", server_host[0]);
        len = strlen(server_str);
        for (int i = 1; i < server_num; i++) {
            snprintf(server_str + len, buf_size - len, "|%s", server_host[i]);
            len = strlen(server_str);
        }

        int err = start_plugin(plugin, plugin_opts, server_str,
                               plugin_port, "127.0.0.1", server_port, MODE_SERVER);
        if (err) {
            FATAL("failed to start the plugin");
        }
    }
#endif

    // initialize listen context
    listen_ctx_t listen_ctx_list[server_num];

    // bind to each interface
    if (mode != UDP_ONLY) {
        for (int i = 0; i < server_num; i++) {
            const char *host = server_host[i];

            if (plugin != NULL) {
                host = "127.0.0.1";
            }

            if (host && strcmp(host, ":") > 0)
                LOGI("tcp server listening at [%s]:%s", host, server_port);
            else
                LOGI("tcp server listening at %s:%s", host ? host : "0.0.0.0", server_port);

            // Bind to port
            int listenfd;

            if (use_kcp) {
                listenfd = create_and_bind(SOCK_DGRAM, host, server_port, mptcp);
                if (listenfd == -1) {
                    FATAL("create() error");
                }
                setfastopen(listenfd);
            }
            else {
                listenfd = create_and_bind(SOCK_STREAM, host, server_port, mptcp);
                if (listenfd == -1) {
                    FATAL("bind() error");
                }
                if (listen(listenfd, SSMAXCONN) == -1) {
                    FATAL("listen() error");
                }
                setfastopen(listenfd);
            }
            setnonblocking(listenfd);
            listen_ctx_t *listen_ctx = &listen_ctx_list[i];

            // Setup proxy context
            listen_ctx->timeout = atoi(timeout);
            listen_ctx->fd      = listenfd;
            listen_ctx->iface   = iface;
            listen_ctx->loop    = loop;
            listen_ctx->use_kcp = use_kcp;

            ev_io_init(&listen_ctx->io, accept_cb, listenfd, EV_READ);
            IO_START(listen_ctx->io, "listener[%d]: + listen", listen_ctx->fd);

            if (plugin != NULL)
                break;
        }
    }

    if (mode != TCP_ONLY) {
        for (int i = 0; i < server_num; i++) {
            const char *host = server_host[i];
            const char *port = server_port;
            if (plugin != NULL) {
                port = plugin_port;
            }
            if (host && strcmp(host, ":") > 0)
                LOGI("udp server listening at [%s]:%s", host, port);
            else
                LOGI("udp server listening at %s:%s", host ? host : "0.0.0.0", port);
            // Setup UDP
            init_udprelay(host, port, mtu, crypto, atoi(timeout), iface);
        }
    }

#ifndef __MINGW32__
    if (manager_addr != NULL) {
        ev_timer_init(&stat_update_watcher, stat_update_cb, UPDATE_INTERVAL, UPDATE_INTERVAL);
        ev_timer_start(EV_DEFAULT, &stat_update_watcher);
    }
#endif

    ev_timer_init(&block_list_watcher, block_list_clear_cb, UPDATE_INTERVAL, UPDATE_INTERVAL);
    ev_timer_start(EV_DEFAULT, &block_list_watcher);

#ifndef __MINGW32__
    // setuid
    if (user != NULL && !run_as(user)) {
        FATAL("failed to switch user");
    }

    if (geteuid() == 0) {
        LOGI("running from root user");
    }
#endif

    // init block list
    init_block_list();

    // Init connections
    cork_dllist_init(&connections);

    // start ev loop
    ev_run(loop, 0);

    if (verbose) {
        LOGI("closed gracefully");
    }

    // Free block list
    free_block_list();

#ifndef __MINGW32__
    if (manager_addr != NULL) {
        ev_timer_stop(EV_DEFAULT, &stat_update_watcher);
    }
#endif

    ev_timer_stop(EV_DEFAULT, &block_list_watcher);

#ifndef __MINGW32__
    if (plugin != NULL) {
        stop_plugin();
    }
#endif

    // Clean up

    resolv_shutdown(loop);

    for (int i = 0; i < server_num; i++) {
        listen_ctx_t *listen_ctx = &listen_ctx_list[i];
        if (mode != UDP_ONLY) {
            IO_STOP(listen_ctx->io, "listener[%d]: - listen", listen_ctx->fd);
            close(listen_ctx->fd);
        }
        if (plugin != NULL)
            break;
    }

    if (mode != UDP_ONLY) {
        free_connections(loop);
    }

    if (mode != TCP_ONLY) {
        free_udprelay();
    }

#ifdef __MINGW32__
    winsock_cleanup();
#endif

    return 0;
}
