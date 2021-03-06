/*
 * local.c - Setup a socks5 proxy through remote shadowsocks server
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
#include <unistd.h>
#include <getopt.h>
#ifndef __MINGW32__
#include <errno.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <netinet/in.h>
#endif
#ifdef LIB_ONLY
#include "shadowsocks.h"
#endif

#if defined(HAVE_SYS_IOCTL_H) && defined(HAVE_NET_IF_H) && defined(__linux__)
#include <net/if.h>
#include <sys/ioctl.h>
#define SET_INTERFACE
#endif

#include <libcork/core.h>

#include "netutils.h"
#include "utils.h"
#include "socks5.h"
#include "acl.h"
#include "http.h"
#include "tls.h"
#include "plugin.h"
#include "local.h"
#include "winsock.h"

#ifndef LIB_ONLY
#ifdef __APPLE__
#include <AvailabilityMacros.h>
#if defined(MAC_OS_X_VERSION_10_10) && MAC_OS_X_VERSION_MIN_REQUIRED >= MAC_OS_X_VERSION_10_10
#include <launch.h>
#define HAVE_LAUNCHD
#endif
#endif
#endif

#ifndef EAGAIN
#define EAGAIN EWOULDBLOCK
#endif

#ifndef EWOULDBLOCK
#define EWOULDBLOCK EAGAIN
#endif

#ifndef DFT_BUF_SIZE
#define DFT_BUF_SIZE (1024 * 2)
#endif

int verbose        = 0;
int reuse_port     = 0;
int keep_resolving = 1;

#ifdef __ANDROID__
int vpn        = 0;
uint64_t tx    = 0;
uint64_t rx    = 0;
ev_tstamp last = 0;
#endif

static crypto_t *crypto;

static int acl       = 0;
static int mode      = TCP_ONLY;
static int ipv6first = 0;
static int fast_open = 0;
static int no_delay  = 0;
static int udp_fd    = 0;

static struct ev_signal sigint_watcher;
static struct ev_signal sigterm_watcher;
#ifndef __MINGW32__
static struct ev_signal sigchld_watcher;
static struct ev_signal sigusr1_watcher;
#endif

#ifdef HAVE_SETRLIMIT
#ifndef LIB_ONLY
static int nofile = 0;
#endif
#endif

static IUINT32 cur_time_ms(void);

static void server_recv_cb(EV_P_ ev_io *w, int revents);
static void server_send_cb(EV_P_ ev_io *w, int revents);
static void remote_recv_cb(EV_P_ ev_io *w, int revents);
static void remote_send_cb(EV_P_ ev_io *w, int revents);
static void accept_cb(EV_P_ ev_io *w, int revents);
static void signal_cb(EV_P_ ev_signal *w, int revents);

static int create_and_bind(const char *addr, const char *port);
#ifdef HAVE_LAUNCHD
static int launch_or_create(const char *addr, const char *port);
#endif
static remote_t *create_remote(listen_ctx_t *listener, struct sockaddr *addr, int direct);
static void free_remote(remote_t *remote);
static void close_and_free_remote(EV_P_ remote_t *remote, uint8_t notify_remote);
static void free_server(server_t *server);
static void close_and_free_server(EV_P_ server_t *server);

static remote_t *new_remote(listen_ctx_t *listener, int fd, int timeout, uint8_t use_kcp);
static server_t *new_server(int fd);

/*Loki: */
extern IUINT32 IKCP_CMD_PUSH /* = 81*/;
extern IUINT32 IKCP_CMD_ACK  /*= 82*/;
extern IUINT32 IKCP_CMD_WASK /*= 83*/;
extern IUINT32 IKCP_CMD_WINS /*= 84*/;
const IUINT32 IKCP_CMD_EXT_SHK = 88;
const IUINT32 IKCP_CMD_EXT_REMOVE = 89;

static int send_to_client(EV_P_ server_t * server, remote_t * remote);
static int kcp_output(const char *buf, int len, ikcpcb *kcp, void *user);
static int kcp_send_cmd(
    listen_ctx_t * listener, server_t * server,
    struct sockaddr * addr, socklen_t addr_len, IUINT32 conv, IUINT32 cmd);
static int kcp_recv_data(server_t * server, remote_t * remote);
static void kcp_log(const char *log, ikcpcb *kcp, void *user);
static void kcp_update_cb(EV_P_ ev_timer *watcher, int revents);
static void kcp_recv_cb(EV_P_ ev_io *w, int revents);
static server_t * kcp_find_server(IUINT32 conv);

static ebb_connection * control_new_connection(ebb_server *server, struct sockaddr_in *addr);
static ebb_request* control_conn_new_request(ebb_connection * ebb_conn);
static void control_conn_on_close(ebb_connection * ebb_conn);
static void control_request_on_complete(ebb_request * ebb_req);

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

static struct cork_dllist connections;

static IUINT32 cur_time_ms(void) {
    struct timeval ptv;
	gettimeofday(&ptv, NULL);
    return (IUINT32)(ptv.tv_usec / 1000) + (IUINT32)ptv.tv_sec * 1000;
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
create_and_bind(const char *addr, const char *port)
{
    struct addrinfo hints;
    struct addrinfo *result, *rp;
    int s, listen_sock;

    memset(&hints, 0, sizeof(struct addrinfo));
    hints.ai_family   = AF_UNSPEC;   /* Return IPv4 and IPv6 choices */
    hints.ai_socktype = SOCK_STREAM; /* We want a TCP socket */
    result            = NULL;

    s = getaddrinfo(addr, port, &hints, &result);

    if (s != 0) {
        LOGI("getaddrinfo: %s", gai_strerror(s));
        return -1;
    }

    if (result == NULL) {
        LOGE("Could not bind");
        return -1;
    }

    for (rp = result; rp != NULL; rp = rp->ai_next) {
        listen_sock = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
        if (listen_sock == -1) {
            continue;
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

        s = bind(listen_sock, rp->ai_addr, rp->ai_addrlen);
        if (s == 0) {
            /* We managed to bind successfully! */
            break;
        }
        else {
            ERROR("bind");
        }

        close(listen_sock);
        listen_sock = -1;
    }

    freeaddrinfo(result);

    return listen_sock;
}

#ifdef HAVE_LAUNCHD
int
launch_or_create(const char *addr, const char *port)
{
    int *fds;
    size_t cnt;
    int error = launch_activate_socket("Listeners", &fds, &cnt);
    if (error == 0) {
        if (cnt == 1) {
            return fds[0];
        }
        else {
            FATAL("please don't specify multi entry");
        }
    }
    else if (error == ESRCH || error == ENOENT) {
        /* ESRCH:  The calling process is not managed by launchd(8).
         * ENOENT: The socket name specified does not exist
         *          in the caller's launchd.plist(5).
         */
        if (port == NULL) {
            usage();
            exit(EXIT_FAILURE);
        }
        return create_and_bind(addr, port);
    }
    else {
        FATAL("launch_activate_socket() error");
    }
    return -1;
}

#endif

static char *
get_name_from_addr(struct sockaddr * addr, socklen_t addr_len, uint8_t with_port) {
    static char name[INET6_ADDRSTRLEN+32] = { 0 };
    memset(name, 0, sizeof(name));
    int port;
    
    if (addr->sa_family == AF_INET) {
        struct sockaddr_in *s = (struct sockaddr_in *)addr;
        inet_ntop(AF_INET, &s->sin_addr, name, INET_ADDRSTRLEN);
        port = ntohs(s->sin_port);
    }
    else if (addr->sa_family == AF_INET6) {
        struct sockaddr_in6 *s = (struct sockaddr_in6 *)addr;
        inet_ntop(AF_INET6, &s->sin6_addr, name, INET6_ADDRSTRLEN);
        port = ntohs(s->sin6_port);
    }
    else {
        return "unknown-family";
    }

    if (with_port) {
        int len = strlen(name);
        snprintf(name + len, sizeof(name) - len, ":%d", port);
    }
    
    return name;
}

static void
free_connections(struct ev_loop *loop)
{
    struct cork_dllist_item *curr, *next;
    cork_dllist_foreach_void(&connections, curr, next) {
        server_t *server = cork_container_of(curr, server_t, entries);
        remote_t *remote = server->remote;
        close_and_free_remote(loop, remote, 0);
        close_and_free_server(loop, server);
    }
}

static void
delayed_connect_cb(EV_P_ ev_timer *watcher, int revents)
{
    server_t *server = cork_container_of(watcher, server_t,
                                         delayed_connect_watcher);

    server_recv_cb(EV_A_ & server->recv_ctx->io, revents);
}

static void
server_recv_cb(EV_P_ ev_io *w, int revents)
{
    server_ctx_t *server_recv_ctx = (server_ctx_t *)w;
    server_t *server              = server_recv_ctx->server;
    remote_t *remote              = server->remote;
    buffer_t *buf;
    ssize_t r;

    TIMER_STOP(server->delayed_connect_watcher, "server[%s]: tcp [- delay connect]", server->name);

    if (remote == NULL) {
        buf = server->buf;
    }
    else {
        if (remote->buf->len != 0) { 
            LOGE("server[%s]: server free(cli recv when buf have left data %d)", server->name, (int)remote->buf->len);
            close_and_free_remote(EV_A_ remote, 1);
            close_and_free_server(EV_A_ server);
            return;
        }

        buf = remote->buf;
    }

    if (revents != EV_TIMER) {
        r = recv(server->fd, buf->data + buf->len, buf->capacity - buf->len, 0);
        if (r == 0) {
            if (verbose) {
                LOGI("server[%s]: server free(cli disconnected)", server->name);
            }
            
            // connection closed
            if (remote && remote->kcp) {
                kcp_send_cmd(
                    server->listener, server, (struct sockaddr *)&remote->addr, (socklen_t)remote->addr_len,
                    remote->kcp->conv, IKCP_CMD_EXT_REMOVE);
            }
            close_and_free_remote(EV_A_ remote, 1);
            close_and_free_server(EV_A_ server);
            return;
        }
        else if (r == -1) {
            if (errno == EAGAIN || errno == EWOULDBLOCK) {
                // no data
                // continue to wait for recv
                return;
            }
            else {
                LOGE("server[%s]: server free(cli recv error %s)", server->name, strerror(errno));
                close_and_free_remote(EV_A_ remote, 1);
                close_and_free_server(EV_A_ server);
                return;
            }
        }

        if (verbose) {
            LOGI("server[%s]: cli >>> %d", server->name, (int)r);
        }
        
        buf->len += r;
    }

    while (1) {
        // local socks5 server
        if (server->stage == STAGE_STREAM) {
            if (remote == NULL) {
                LOGE("server[%s]: server free(no remote)", server->name);
                close_and_free_server(EV_A_ server);
                return;
            }

            // insert shadowsocks header
            if (!remote->direct) {
#ifdef __ANDROID__
                tx += remote->buf->len;
#endif
                int err = crypto->encrypt(remote->buf, server->e_ctx, remote->buf->capacity);

                if (err) {
                    LOGE("server[%s]: server free(invalid password or cipher)", server->name);
                    close_and_free_remote(EV_A_ remote, 1);
                    close_and_free_server(EV_A_ server);
                    return;
                }

                if (server->abuf) {
                    bprepend(remote->buf, server->abuf, remote->buf->capacity);
                    bfree(server->abuf);
                    ss_free(server->abuf);
                    server->abuf = NULL;
                }
            }

            if (!remote->kcp && !remote->send_ctx->connected) {
#ifdef __ANDROID__
                if (vpn) {
                    int not_protect = 0;
                    if (remote->addr.ss_family == AF_INET) {
                        struct sockaddr_in *s = (struct sockaddr_in *)&remote->addr;
                        if (s->sin_addr.s_addr == inet_addr("127.0.0.1"))
                            not_protect = 1;
                    }
                    if (!not_protect) {
                        if (verbose) {
                            LOGI("server[%s]: tcp: protect socket", server->name);
                        }
                        if (protect_socket(remote->fd) == -1) {
                            LOGE("server[%s]: server free(tcp protect socket error)", server->name);
                            close_and_free_remote(EV_A_ remote, 0);
                            close_and_free_server(EV_A_ server);
                            return;
                        }
                    }
                }
#endif

                remote->buf->idx = 0;

                if (!fast_open || remote->direct) {
                    // connecting, wait until connected
                    int r = connect(remote->fd, (struct sockaddr *)&(remote->addr), remote->addr_len);

                    if (r == -1 && errno != CONNECT_IN_PROGRESS) {
                        LOGE("server[%s]: server free(remote connect error %s)", server->name, strerror(errno));
                        close_and_free_remote(EV_A_ remote, 0);
                        close_and_free_server(EV_A_ server);
                        return;
                    }

                    // wait on remote connected event
                    IO_STOP(server_recv_ctx->io, "server[%s]: cli [- >>>] | remote connect in process", server->name);
                    if (!remote->kcp) IO_START(remote->send_ctx->io, "server[%s]: tcp [+ >>>] | remote connect in process", server->name);
                    TIMER_START(remote->send_ctx->watcher, "server[%s]: %s: [+ timeout]", server->name, remote->kcp ? "udp" : "tcp");
                }
                else {
#if defined(MSG_FASTOPEN) && !defined(TCP_FASTOPEN_CONNECT)
                    int s = -1;
                    s = sendto(remote->fd, remote->buf->data, remote->buf->len, MSG_FASTOPEN,
                                   (struct sockaddr *)&(remote->addr), remote->addr_len);
#elif defined(TCP_FASTOPEN_WINSOCK)
                    DWORD s = -1;
                    DWORD err = 0;
                    do {
                        int optval = 1;
                        // Set fast open option
                        if (setsockopt(remote->fd, IPPROTO_TCP, TCP_FASTOPEN,
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
                        if (winsock_dummybind(remote->fd,
                                              (struct sockaddr *)&(remote->addr)) != 0) {
                            ERROR("bind");
                            break;
                        }
                        // Call ConnectEx to send data
                        memset(&remote->olap, 0, sizeof(remote->olap));
                        remote->connect_ex_done = 0;
                        if (ConnectEx(remote->fd, (const struct sockaddr *)&(remote->addr),
                                      remote->addr_len, remote->buf->data, remote->buf->len,
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
#if defined(CONNECT_DATA_IDEMPOTENT)
                    ((struct sockaddr_in *)&(remote->addr))->sin_len = sizeof(struct sockaddr_in);
                    sa_endpoints_t endpoints;
                    memset((char *)&endpoints, 0, sizeof(endpoints));
                    endpoints.sae_dstaddr    = (struct sockaddr *)&(remote->addr);
                    endpoints.sae_dstaddrlen = remote->addr_len;

                    s = connectx(remote->fd, &endpoints, SAE_ASSOCID_ANY,
                                     CONNECT_RESUME_ON_READ_WRITE | CONNECT_DATA_IDEMPOTENT,
                                     NULL, 0, NULL, NULL);
#elif defined(TCP_FASTOPEN_CONNECT)
                    int optval = 1;
                    if(setsockopt(remote->fd, IPPROTO_TCP, TCP_FASTOPEN_CONNECT,
                                (void *)&optval, sizeof(optval)) < 0)
                        FATAL("failed to set TCP_FASTOPEN_CONNECT");
                    s = connect(remote->fd, (struct sockaddr *)&(remote->addr), remote->addr_len);
#else
                    FATAL("fast open is not enabled in this build");
#endif
                    if (s == 0) {
                        s = send(remote->fd, remote->buf->data, remote->buf->len, 0);
                    }
#endif
                    if (s == -1) {
                        if (errno == CONNECT_IN_PROGRESS) {
                            // in progress, wait until connected
                            remote->buf->idx = 0;
                            IO_STOP(server_recv_ctx->io, "server[%s]: cli [- >>>] | connect in process", server->name);
                            if (!remote->kcp) IO_START(remote->send_ctx->io, "server[%s]: tcp [+ >>>] | connect in process", server->name);
                            return;
                        }
                        else {
                            if (errno == EOPNOTSUPP || errno == EPROTONOSUPPORT || errno == ENOPROTOOPT) {
                                LOGE("server[%s]: fast open is not supported on this platform", server->name);
                                // just turn it off
                                fast_open = 0;
                            }
                            else {
                                LOGE("server[%s]: server free(fast_open_connect)", server->name);
                            }
                            close_and_free_remote(EV_A_ remote, 0);
                            close_and_free_server(EV_A_ server);
                            return;
                        }
                    }
                    else {
                        remote->buf->len -= s;
                        remote->buf->idx  = s;

                        IO_STOP(server_recv_ctx->io, "server[%s]: cli [- >>>] | send to remote in process", server->name);
                        if (!remote->kcp) IO_START(remote->send_ctx->io, "server[%s]: tcp [+ >>>] | send to remote in process", server->name);
                        TIMER_START(remote->send_ctx->watcher, "server[%s]: %s [+ timeout] | send to remote in process", server->name, remote->kcp ? "udp" : "tcp");
                        return;
                    }
                }
            }
            else {
                if (remote->kcp) {
                    int s = ikcp_send(remote->kcp, remote->buf->data, remote->buf->len);
                    if (s < 0) {
                        LOGE("server[%s]: server free(kcp send error %d)", server->name, s);
                        close_and_free_remote(EV_A_ remote, 1);
                        close_and_free_server(EV_A_ server);
                        return;
                    }
                    
                    if (verbose) {
                        LOGI("server[%s]: kcp     >>> %d", server->name, (int)remote->buf->len);
                    }

                    remote->buf->idx = 0;
                    remote->buf->len = 0;
                }
                else {
                    int s = send(remote->fd, remote->buf->data, remote->buf->len, 0);
                    if (s == -1) {
                        if (errno == EAGAIN || errno == EWOULDBLOCK) {
                            // no data, wait for send
                            remote->buf->idx = 0;
                            IO_STOP(server_recv_ctx->io, "server[%s]: cli [- >>>] | send to remote block", server->name);
                            if (!remote->kcp) IO_START(remote->send_ctx->io, "server[%s]: tcp [+ >>>] | send to remote block", server->name);
                            return;
                        }
                        else {
                            LOGE("server[%s]: server free(send to remote error %s)", server->name, strerror(errno));
                            close_and_free_remote(EV_A_ remote, 1);
                            close_and_free_server(EV_A_ server);
                            return;
                        }
                    }
                    else if (s < (int)(remote->buf->len)) {
                        remote->buf->len -= s;
                        remote->buf->idx  = s;
                        IO_STOP(server_recv_ctx->io, "server[%s]: cli [- >>>] | send to remote in process", server->name);
                        if (!remote->kcp) IO_START(remote->send_ctx->io, "server[%s]: tcp [+ >>>] | send to remote in process", server->name);
                        return;
                    }
                    else {
                        remote->buf->idx = 0;
                        remote->buf->len = 0;
                    }
                }
            }
            // all processed
            return;
        }
        else if (server->stage == STAGE_INIT) {
            if (buf->len < 1)
                return;
            if (buf->data[0] != SVERSION) {
                LOGE("server[%s]: server free(version mismatch)", server->name);
                close_and_free_remote(EV_A_ remote, 0);
                close_and_free_server(EV_A_ server);
                return;
            }
            if (buf->len < sizeof(struct method_select_request)) {
                return;
            }
            struct method_select_request *method = (struct method_select_request *)buf->data;
            int method_len                       = method->nmethods + sizeof(struct method_select_request);
            if (buf->len < method_len) {
                return;
            }

            struct method_select_response response;
            response.ver    = SVERSION;
            response.method = METHOD_UNACCEPTABLE;
            for (int i = 0; i < method->nmethods; i++)
                if (method->methods[i] == METHOD_NOAUTH) {
                    response.method = METHOD_NOAUTH;
                    break;
                }
            char *send_buf = (char *)&response;
            send(server->fd, send_buf, sizeof(response), 0);
            if (response.method == METHOD_UNACCEPTABLE) {
                LOGE("server[%s]: server free(response.method)", server->name);
                close_and_free_remote(EV_A_ remote, 0);
                close_and_free_server(EV_A_ server);
                return;
            }

            server->stage = STAGE_HANDSHAKE;

            if (method_len < (int)(buf->len)) {
                memmove(buf->data, buf->data + method_len, buf->len - method_len);
                buf->len -= method_len;
                continue;
            }

            buf->len = 0;
            return;
        }
        else if (server->stage == STAGE_HANDSHAKE
                 || server->stage == STAGE_PARSE
                 || server->stage == STAGE_SNI)
        {
            struct socks5_request *request = (struct socks5_request *)buf->data;
            size_t request_len             = sizeof(struct socks5_request);
            struct sockaddr_in sock_addr;
            memset(&sock_addr, 0, sizeof(sock_addr));

            if (buf->len < request_len) {
                return;
            }

            int udp_assc = 0;

            if (request->cmd == 3) {
                udp_assc = 1;
                socklen_t addr_len = sizeof(sock_addr);
                getsockname(udp_fd, (struct sockaddr *)&sock_addr,
                            &addr_len);
                if (verbose) {
                    LOGI("udp assc request accepted");
                }
            }
            else if (request->cmd != 1) {
                LOGE("server[%s]: server free(unsupported cmd: %d)", server->name, request->cmd);
                struct socks5_response response;
                response.ver  = SVERSION;
                response.rep  = CMD_NOT_SUPPORTED;
                response.rsv  = 0;
                response.atyp = 1;
                char *send_buf = (char *)&response;
                send(server->fd, send_buf, 4, 0);
                close_and_free_remote(EV_A_ remote, 0);
                close_and_free_server(EV_A_ server);
                return;
            }

            // Fake reply
            if (server->stage == STAGE_HANDSHAKE) {
                struct socks5_response response;
                response.ver  = SVERSION;
                response.rep  = 0;
                response.rsv  = 0;
                response.atyp = 1;

                buffer_t resp_to_send;
                buffer_t *resp_buf = &resp_to_send;
                balloc(resp_buf, 2048);

                memcpy(resp_buf->data, &response, sizeof(struct socks5_response));
                memcpy(resp_buf->data + sizeof(struct socks5_response),
                       &sock_addr.sin_addr, sizeof(sock_addr.sin_addr));
                memcpy(resp_buf->data + sizeof(struct socks5_response) +
                       sizeof(sock_addr.sin_addr),
                       &sock_addr.sin_port, sizeof(sock_addr.sin_port));

                int reply_size = sizeof(struct socks5_response) +
                                 sizeof(sock_addr.sin_addr) + sizeof(sock_addr.sin_port);

                int s = send(server->fd, resp_buf->data, reply_size, 0);

                bfree(resp_buf);

                if (s < reply_size) {
                    LOGE("server[%s]: server free(failed to send fake reply)", server->name);
                    close_and_free_remote(EV_A_ remote, 0);
                    close_and_free_server(EV_A_ server);
                    return;
                }
                if (udp_assc) {
                    // Wait until client closes the connection
                    return;
                }

                server->stage = STAGE_PARSE;
            }

            char host[257], ip[INET6_ADDRSTRLEN], port[16];

            buffer_t *abuf = server->abuf;
            abuf->idx = 0;
            abuf->len = 0;

            abuf->data[abuf->len++] = request->atyp;
            int atyp = request->atyp;

            // get remote addr and port
            if (atyp == 1) {
                // IP V4
                size_t in_addr_len = sizeof(struct in_addr);
                if (buf->len < request_len + in_addr_len + 2) {
                    return;
                }
                memcpy(abuf->data + abuf->len, buf->data + request_len, in_addr_len + 2);
                abuf->len += in_addr_len + 2;

                if (acl || verbose) {
                    uint16_t p;
                    memcpy(&p, buf->data + request_len + in_addr_len, sizeof(uint16_t));
                    p = ntohs(p);
                    inet_ntop(AF_INET, (const void *)(buf->data + request_len), ip, INET_ADDRSTRLEN);
                    sprintf(port, "%d", p);
                }
            }
            else if (atyp == 3) {
                // Domain name
                uint8_t name_len = *(uint8_t *)(buf->data + request_len);
                if (buf->len < request_len + 1 + name_len + 2) {
                    return;
                }
                abuf->data[abuf->len++] = name_len;
                memcpy(abuf->data + abuf->len, buf->data + request_len + 1, name_len + 2);
                abuf->len += name_len + 2;

                if (acl || verbose) {
                    uint16_t p;
                    memcpy(&p, buf->data + request_len + 1 + name_len, sizeof(uint16_t));
                    p = ntohs(p);
                    memcpy(host, buf->data + request_len + 1, name_len);
                    host[name_len] = '\0';
                    sprintf(port, "%d", p);
                }
            }
            else if (atyp == 4) {
                // IP V6
                size_t in6_addr_len = sizeof(struct in6_addr);
                if (buf->len < request_len + in6_addr_len + 2) {
                    return;
                }
                memcpy(abuf->data + abuf->len, buf->data + request_len, in6_addr_len + 2);
                abuf->len += in6_addr_len + 2;

                if (acl || verbose) {
                    uint16_t p;
                    memcpy(&p, buf->data + request_len + in6_addr_len, sizeof(uint16_t));
                    p = ntohs(p);
                    inet_ntop(AF_INET6, (const void *)(buf->data + request_len), ip, INET6_ADDRSTRLEN);
                    sprintf(port, "%d", p);
                }
            }
            else {
                LOGE("server[%s]: server free(unsupported addrtype: %d)", server->name, request->atyp);
                close_and_free_remote(EV_A_ remote, 0);
                close_and_free_server(EV_A_ server);
                return;
            }

            size_t abuf_len  = abuf->len;
            int sni_detected = 0;
            int ret          = 0;

            char *hostname;
            uint16_t dst_port;

            memcpy(&dst_port, abuf->data + abuf->len - 2, sizeof(uint16_t));
            dst_port = ntohs(dst_port);

            if (atyp == 1 || atyp == 4) {
                if (dst_port == http_protocol->default_port)
                    ret = http_protocol->parse_packet(buf->data + 3 + abuf->len,
                                                      buf->len - 3 - abuf->len, &hostname);
                else if (dst_port == tls_protocol->default_port)
                    ret = tls_protocol->parse_packet(buf->data + 3 + abuf->len,
                                                     buf->len - 3 - abuf->len, &hostname);
                if (ret == -1 && buf->len < buf->capacity && server->stage != STAGE_SNI) {
                    server->stage = STAGE_SNI;
                    TIMER_START(server->delayed_connect_watcher, "server[%s]: tcp [+ delay connect]", server->name);
                    return;
                }
                else if (ret > 0) {
                    sni_detected = 1;
                    if (acl || verbose) {
                        memcpy(host, hostname, ret);
                        host[ret] = '\0';
                    }
                    ss_free(hostname);
                }
            }

            server->stage = STAGE_STREAM;

            buf->len -= (3 + abuf_len);
            if (buf->len > 0) {
                memmove(buf->data, buf->data + 3 + abuf_len, buf->len);
            }

            if (verbose) {
                if (sni_detected || atyp == 3)
                    LOGI("server[%s]: connect to %s:%s", server->name, host, port);
                else if (atyp == 1)
                    LOGI("server[%s]: connect to %s:%s", server->name, ip, port);
                else if (atyp == 4)
                    LOGI("server[%s]: connect to [%s]:%s", server->name, ip, port);
            }

            if (acl
#ifdef __ANDROID__
                && !(vpn && strcmp(port, "53") == 0)
#endif
                ) {
                int bypass     = 0;
                int resolved   = 0;
                struct sockaddr_storage storage;
                memset(&storage, 0, sizeof(struct sockaddr_storage));
                int err;

                int host_match = 0;
                if (sni_detected || atyp == 3)
                    host_match = acl_match_host(host);

                if (host_match > 0)
                    bypass = 1;                 // bypass hostnames in black list
                else if (host_match < 0)
                    bypass = 0;                 // proxy hostnames in white list
                else {
#ifndef __ANDROID__
                    if (atyp == 3) {            // resolve domain so we can bypass domain with geoip
                        err = get_sockaddr(host, port, &storage, 0, ipv6first);
                        if (err != -1) {
                            resolved = 1;
                            switch (((struct sockaddr *)&storage)->sa_family) {
                            case AF_INET:
                            {
                                struct sockaddr_in *addr_in = (struct sockaddr_in *)&storage;
                                inet_ntop(AF_INET, &(addr_in->sin_addr), ip, INET_ADDRSTRLEN);
                                break;
                            }
                            case AF_INET6:
                            {
                                struct sockaddr_in6 *addr_in6 = (struct sockaddr_in6 *)&storage;
                                inet_ntop(AF_INET6, &(addr_in6->sin6_addr), ip, INET6_ADDRSTRLEN);
                                break;
                            }
                            default:
                                break;
                            }
                        }
                    }
#endif
                    int ip_match = acl_match_host(ip);
                    switch (get_acl_mode()) {
                    case BLACK_LIST:
                        if (ip_match > 0)
                            bypass = 1;                   // bypass IPs in black list
                        break;
                    case WHITE_LIST:
                        bypass = 1;
                        if (ip_match < 0)
                            bypass = 0;                   // proxy IPs in white list
                        break;
                    }
                }

                if (bypass) {
                    if (verbose) {
                        if (sni_detected || atyp == 3)
                            LOGI("bypass %s:%s", host, port);
                        else if (atyp == 1)
                            LOGI("bypass %s:%s", ip, port);
                        else if (atyp == 4)
                            LOGI("bypass [%s]:%s", ip, port);
                    }
#ifndef __ANDROID__
                    if (atyp == 3 && resolved != 1)
                        err = get_sockaddr(host, port, &storage, 0, ipv6first);
                    else
#endif
                    err = get_sockaddr(ip, port, &storage, 0, ipv6first);
                    if (err != -1) {
                        remote = create_remote(server->listener, (struct sockaddr *)&storage, 1);
                    }
                }
            }

            // Not bypass
            if (remote == NULL) {
                remote = create_remote(server->listener, NULL, 0);
            }

            if (remote == NULL) {
                LOGE("server[%s]: server free(create remote error)", server->name);
                close_and_free_server(EV_A_ server);
                return;
            }

            if (!remote->direct) {
                int err = crypto->encrypt(abuf, server->e_ctx, abuf->capacity);
                if (err) {
                    LOGE("server[%s]: server free(invalid password or cipher)", server->name);
                    close_and_free_remote(EV_A_ remote, 0);
                    close_and_free_server(EV_A_ server);
                    return;
                }
            }

            if (buf->len > 0) {
                memcpy(remote->buf->data, buf->data, buf->len);
                remote->buf->len = buf->len;
                buf->len = 0;
            }

            server->remote = remote;
            remote->server = server;

            if (remote->kcp) {
                snprintf(server->name, sizeof(server->name), "%d-%d", server->fd, (int)remote->kcp->conv);

                TIMER_START(remote->recv_ctx->watcher, "server[%s]: udp [+ <<< timeout]", server->name);
            }
            
            /*Loki: kcp*/
            if (buf->len > 0 || sni_detected) {
                continue;
            }
            else {
                TIMER_START(server->delayed_connect_watcher, "server[%s]: tcp [+ delay connect]", server->name);
            }

            return;
        }
    }
}

static void
server_send_cb(EV_P_ ev_io *w, int revents)
{
    server_ctx_t *server_send_ctx = (server_ctx_t *)w;
    server_t *server              = server_send_ctx->server;
    remote_t *remote              = server->remote;
    if (server->buf->len == 0) {
        // close and free
        LOGE("server[%s]: server free(cli send with buf 0)", server->name);
        close_and_free_remote(EV_A_ remote, 1);
        close_and_free_server(EV_A_ server);
        return;
    }
    else {
        // has data to send
        ssize_t s = send(server->fd, server->buf->data + server->buf->idx, server->buf->len, 0);
        if (s == -1) {
            if (errno != EAGAIN && errno != EWOULDBLOCK) {
                LOGE("server[%s]: server free(cli send error %s)", server->name, strerror(errno));
                close_and_free_remote(EV_A_ remote, 1);
                close_and_free_server(EV_A_ server);
            }
            return;
        }
        else if (s < (ssize_t)(server->buf->len)) {
            // partly sent, move memory, wait for the next time to send

            server->buf->len -= s;
            server->buf->idx += s;

            if (verbose) {
                LOGI("server[%s]: cli <<< %d | %d", server->name, (int)s, (int)server->buf->len);
            }
            
            return;
        }
        else {
            // all sent out, wait for reading
            server->buf->len = 0;
            server->buf->idx = 0;

            if (verbose) {
                LOGI("server[%s]: cli <<< %d", server->name, (int)s);
            }

            if (remote && remote->kcp) {
                if (kcp_recv_data(server, remote) != 0) {
                    close_and_free_remote(EV_A_ remote, 1);
                    close_and_free_server(EV_A_ server);
                    return;
                }

                if (server->buf->len > 0) {
                    if (send_to_client(EV_A_ server, remote) != 0) {
                        close_and_free_remote(EV_A_ remote, 1);
                        close_and_free_server(EV_A_ server);
                        return;
                    }
                }
            }

            if (server->buf->len == 0) {
                IO_STOP(server_send_ctx->io, "server[%s]: cli [- <<<] | cli response no data", server->name);
                if (!remote->kcp) IO_START(remote->recv_ctx->io, "server[%s]: %s [+ <<<] | cli response no data", server->name, "tcp");
            }
            
            return;
        }
    }
}

#ifdef __ANDROID__
void
stat_update_cb()
{
    ev_tstamp now = ev_time();
    if (now - last > 0.5) {
        send_traffic_stat(tx, rx);
        last = now;
    }
}

#endif

static void
remote_timeout_cb(EV_P_ ev_timer *watcher, int revents) {
    remote_ctx_t *remote_ctx = cork_container_of(watcher, remote_ctx_t, watcher);
    remote_t *remote = remote_ctx->remote;
    server_t *server = remote->server;

    LOGE("server[%s]: server free(%s connection timeout)", server->name, remote->kcp ? "udp" : "tcp");

    close_and_free_remote(EV_A_ remote, 1);
    close_and_free_server(EV_A_ server);
}

static void
remote_recv_cb(EV_P_ ev_io *w, int revents)
{
    remote_ctx_t *remote_recv_ctx = (remote_ctx_t *)w;
    remote_t *remote              = remote_recv_ctx->remote;
    server_t *server              = remote->server;

    ev_timer_again(EV_A_ & remote->recv_ctx->watcher);

    if (server->buf->len > 0) {
        LOGE("server[%s]: server free(tcp receive with buf len %d)", server->name, (int)server->buf->len); 
        close_and_free_remote(EV_A_ remote, 1);
        close_and_free_server(EV_A_ server);
        return;
    }
    
    ssize_t r = recv(remote->fd, server->buf->data, server->buf->capacity, 0);
    if (r == 0) {
        if (verbose) {
            LOGI("server[%s]: server free(tcp connection colsed)", server->name);
        }
        close_and_free_remote(EV_A_ remote, 1);
        close_and_free_server(EV_A_ server);
        return;
    }
    else if (r == -1) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            // no data
            // continue to wait for recv
            return;
        }
        else {
            LOGE("server[%s]: server free(tcp recv error %s)", server->name, strerror(errno)); 
            close_and_free_remote(EV_A_ remote, 1);
            close_and_free_server(EV_A_ server);
            return;
        }
    }

    if (verbose) {
        LOGI("server[%s]: tcp    <<< %d", server->name, (int)r);
    }
    
    server->buf->len = r;
    if (send_to_client(EV_A_ server, remote) != 0) {
        close_and_free_remote(EV_A_ remote, 1);
        close_and_free_server(EV_A_ server);
        return;
    }
}

static void
remote_send_cb(EV_P_ ev_io *w, int revents)
{
    remote_t *remote              = ((remote_ctx_t *)w)->remote;
    server_t *server              = remote->server;

    /*Loki: kcp*/
    assert(remote->kcp == NULL);
    /**/

    LOGI("server[%s]: remote_send_cb: revents=%x", server->name, revents);

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
                }
                else if (WSAGetLastError() == WSA_IO_INCOMPLETE) {
                    // XXX: ConnectEx still not connected, wait for next time
                    return;
                }
                else {
                    ERROR("WSAGetOverlappedResult");
                    // not connected
                    close_and_free_remote(EV_A_ remote, 0);
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
        socklen_t len = sizeof(addr);
        int r         = getpeername(remote->fd, (struct sockaddr *)&addr, &len);
        if (r == 0) {
            remote->send_ctx->connected = 1;
            TIMER_STOP(remote->send_ctx->watcher, "server[%s]: tcp [+ >>> timeout]", server->name);
            TIMER_START(remote->recv_ctx->watcher, "server[%s]: tcp [+ <<< timeout]", server->name);
            assert(!remote->kcp);
            IO_START(remote->recv_ctx->io, "server[%s]: tcp [+ >>>] | getpeername complete", server->name);

            // no need to send any data
            if (remote->buf->len == 0) {
                IO_STOP(remote->send_ctx->io, "server[%s]: tcp [- >>>] | cli no data", server->name);
                IO_START(server->recv_ctx->io, "server[%s]: cli [+ >>>] | cli no data", server->name);
                return;
            }
        }
        else {
            // not connected
            LOGE("server[%s]: server free(tcp getpeername error %s)", server->name, strerror(errno));
            close_and_free_remote(EV_A_ remote, 1);
            close_and_free_server(EV_A_ server);
            return;
        }
    }

    if (remote->buf->len == 0) {
        // close and free
        if (verbose) {
            LOGI("server[%s]: server free(no send data)", server->name);
        }
        close_and_free_remote(EV_A_ remote, 1);
        close_and_free_server(EV_A_ server);
        return;
    }
    else {
        if (remote->kcp) {
            int s = ikcp_send(remote->kcp, remote->buf->data + remote->buf->idx, remote->buf->len);
            if (s < 0) {
                LOGE("server[%s]: server free(kcp send error %d)", server->name, s);
                close_and_free_remote(EV_A_ remote, 1);
                close_and_free_server(EV_A_ server);
                return;
            }
            
            if (verbose) {
                LOGI("server[%s]: kcp     >>> %d", server->name, (int)remote->buf->len);
            }
        
            remote->buf->len = 0;
            remote->buf->idx = 0;
            IO_STOP(remote->send_ctx->io, "server[%s]: tcp [- >>>] | remote send complete", server->name);
            IO_START(server->recv_ctx->io, "server[%s]: cli [+ >>>] | remote send complete", server->name);
        }
        else {
            ssize_t s = send(remote->fd, remote->buf->data + remote->buf->idx, remote->buf->len, 0);
            if (s == -1) {
                if (errno != EAGAIN && errno != EWOULDBLOCK) {
                    LOGE("server[%s]: server free(send to remote error %s)", server->name, strerror(errno));
                    close_and_free_remote(EV_A_ remote, 1);
                    close_and_free_server(EV_A_ server);
                }
                return;
            }
            else if (s < (ssize_t)(remote->buf->len)) {
                // partly sent, move memory, wait for the next time to send
                remote->buf->len -= s;
                remote->buf->idx += s;
                return;
            }
            else {
                // all sent out, wait for reading
                remote->buf->len = 0;
                remote->buf->idx = 0;
                IO_STOP(remote->send_ctx->io, "server[%s]: tcp [- >>>] | remote send complete", server->name);
                IO_START(server->recv_ctx->io, "server[%s]: cli [+ >>>] | remote send complete", server->name);
            }
        }
    }
}

static remote_t *
new_remote(listen_ctx_t *listener, int fd, int timeout, uint8_t use_kcp)
{
    remote_t *remote;
    remote = ss_malloc(sizeof(remote_t));

    memset(remote, 0, sizeof(remote_t));

    remote->buf      = ss_malloc(sizeof(buffer_t));
    remote->recv_ctx = ss_malloc(sizeof(remote_ctx_t));
    remote->send_ctx = ss_malloc(sizeof(remote_ctx_t));
    balloc(remote->buf, DFT_BUF_SIZE);
    memset(remote->recv_ctx, 0, sizeof(remote_ctx_t));
    memset(remote->send_ctx, 0, sizeof(remote_ctx_t));
    remote->recv_ctx->connected = 0;
    remote->send_ctx->connected = 0;
    remote->fd                  = fd;
    remote->recv_ctx->remote    = remote;
    remote->send_ctx->remote    = remote;

    /*Loki: init kcmp*/
    if (use_kcp) {
        static int conv = 1;
        remote->kcp                 = ikcp_create(conv, remote);
        conv++;
    
        remote->kcp->output	= kcp_output;

        if (verbose) {
            remote->kcp->writelog = kcp_log;
            remote->kcp->logmask = 0xffffffff;
        }

        ikcp_wndsize(
            remote->kcp,
            listener->kcp_sndwnd,
            listener->kcp_rcvwnd);

        ikcp_nodelay(
            remote->kcp,
            listener->kcp_nodelay, listener->kcp_interval,
            listener->kcp_resend, listener->kcp_nc);

        remote->kcp_last_send_ms = cur_time_ms();
    }
    else {
        remote->kcp = NULL;
    }
    /**/

    ev_io_init(&remote->recv_ctx->io, remote_recv_cb, fd, EV_READ);
    ev_io_init(&remote->send_ctx->io, remote_send_cb, fd, EV_WRITE);
    ev_timer_init(&remote->send_ctx->watcher, remote_timeout_cb, min(MAX_CONNECT_TIMEOUT, timeout), 0);
    ev_timer_init(&remote->recv_ctx->watcher, remote_timeout_cb, timeout, timeout);

    return remote;
}

static void
free_remote(remote_t *remote)
{
    if (remote->server != NULL) {
        remote->server->remote = NULL;
        snprintf(remote->server->name, sizeof(remote->server->name), "%d", remote->server->fd);
    }
    if (remote->buf != NULL) {
        bfree(remote->buf);
        ss_free(remote->buf);
    }
    /*Loki: kcp*/
    if (remote->kcp != NULL) {
        ikcp_release(remote->kcp);
        remote->kcp = NULL;
    }
    /**/
    
    ss_free(remote->recv_ctx);
    ss_free(remote->send_ctx);
    ss_free(remote);
}

static void
close_and_free_remote(EV_P_ remote_t *remote, uint8_t notify_remote)
{
    if (remote != NULL) {
        if (notify_remote && remote->kcp && remote->server) {
            kcp_send_cmd(
                remote->server->listener, remote->server, (struct sockaddr *)&remote->addr, (socklen_t)remote->addr_len,
                remote->kcp->conv, IKCP_CMD_EXT_REMOVE);
        }
        
        TIMER_STOP(remote->send_ctx->watcher, "server[%s]: %s [- >>> timeout]", remote->server->name, remote->kcp ? "udp" : "tcp");
        TIMER_STOP(remote->recv_ctx->watcher, "server[%s]: %s [- <<< timeout]", remote->server->name, remote->kcp ? "udp" : "tcp");
        IO_STOP(remote->send_ctx->io, "server[%s]: %s [- >>>] | remote free", remote->server->name, remote->kcp ? "udp" : "tcp");
        IO_STOP(remote->recv_ctx->io, "server[%s]: %s [- <<<] | remote free", remote->server->name, remote->kcp ? "udp" : "tcp");
        close(remote->fd);
        free_remote(remote);
    }
}

static server_t *
new_server(int fd)
{
    server_t *server;
    server = ss_malloc(sizeof(server_t));

    memset(server, 0, sizeof(server_t));

    server->recv_ctx = ss_malloc(sizeof(server_ctx_t));
    server->send_ctx = ss_malloc(sizeof(server_ctx_t));
    server->buf      = ss_malloc(sizeof(buffer_t));
    server->buf->len = 0;
    server->buf->idx = 0;
    server->abuf     = ss_malloc(sizeof(buffer_t));
    balloc(server->buf, DFT_BUF_SIZE);
    balloc(server->abuf, 2048);
    memset(server->recv_ctx, 0, sizeof(server_ctx_t));
    memset(server->send_ctx, 0, sizeof(server_ctx_t));
    server->stage               = STAGE_INIT;
    server->fd                  = fd;
    server->recv_ctx->server    = server;
    server->send_ctx->server    = server;
    snprintf(server->name, sizeof(server->name), "%d", fd);

    server->e_ctx = ss_align(sizeof(cipher_ctx_t));
    server->d_ctx = ss_align(sizeof(cipher_ctx_t));
    crypto->ctx_init(crypto->cipher, server->e_ctx, 1);
    crypto->ctx_init(crypto->cipher, server->d_ctx, 0);

    ev_io_init(&server->recv_ctx->io, server_recv_cb, fd, EV_READ);
    ev_io_init(&server->send_ctx->io, server_send_cb, fd, EV_WRITE);

    ev_timer_init(&server->delayed_connect_watcher,
                  delayed_connect_cb, 0.05, 0);

    cork_dllist_add(&connections, &server->entries);

    return server;
}

static void
free_server(server_t *server)
{
    if (verbose) {
        LOGI("server[%s]: free", server->name);
    }
    
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
    if (server->abuf != NULL) {
        bfree(server->abuf);
        ss_free(server->abuf);
    }
    ss_free(server->recv_ctx);
    ss_free(server->send_ctx);
    ss_free(server);
}

static void
close_and_free_server(EV_P_ server_t *server)
{
    if (server != NULL) {
        IO_STOP(server->send_ctx->io, "server[%s]: cli [- <<<] | server free", server->name);
        IO_STOP(server->recv_ctx->io, "server[%s]: cli [- >>>] | server free", server->name);
        TIMER_STOP(server->delayed_connect_watcher, "server[%s]: tcp [- delay connect]", server->name);
        close(server->fd);
        free_server(server);
    }
}

static remote_t *
create_remote(listen_ctx_t *listener, struct sockaddr *addr, int direct)
{
    struct sockaddr *remote_addr;

    int index = rand() % listener->remote_num;
    if (addr == NULL) {
        remote_addr = listener->remote_addr[index];
    }
    else {
        remote_addr = addr;
    }

    uint8_t use_kcp = !direct && listener->use_kcp;

    int remotefd;
    if (use_kcp) {
        remotefd = -1;
    }
    else {
        remotefd = socket(remote_addr->sa_family, SOCK_STREAM, IPPROTO_TCP);
        if (remotefd == -1) {
            ERROR("socket");
            return NULL;
        }

        int opt = 1;
        setsockopt(remotefd, SOL_TCP, TCP_NODELAY, &opt, sizeof(opt));
#ifdef SO_NOSIGPIPE
        setsockopt(remotefd, SOL_SOCKET, SO_NOSIGPIPE, &opt, sizeof(opt));
#endif

        if (listener->mptcp > 1) {
            int err = setsockopt(remotefd, SOL_TCP, listener->mptcp, &opt, sizeof(opt));
            if (err == -1) {
                ERROR("failed to enable multipath TCP");
            }
        }
        else if (listener->mptcp == 1) {
            int i = 0;
            while ((listener->mptcp = mptcp_enabled_values[i]) > 0) {
                int err = setsockopt(remotefd, SOL_TCP, listener->mptcp, &opt, sizeof(opt));
                if (err != -1) {
                    break;
                }
                i++;
            }
            if (listener->mptcp == 0) {
                ERROR("failed to enable multipath TCP");
            }
        }
    }
    
    // Setup
    setnonblocking(remotefd);
#ifdef SET_INTERFACE
    if (listener->iface) {
        if (setinterface(remotefd, listener->iface) == -1)
            ERROR("setinterface");
    }
#endif

    remote_t *remote = new_remote(listener, remotefd, listener->timeout, use_kcp);
    remote->addr_len = get_sockaddr_len(remote_addr);
    memcpy(&(remote->addr), remote_addr, remote->addr_len);

    if (remote->kcp) {
        snprintf(
            remote->peer_name, sizeof(remote->peer_name) - 1,
            "%s.%d", get_name_from_addr(remote_addr, remote->addr_len, 1), (int)remote->kcp->conv);
    }
    else {
        snprintf(
            remote->peer_name, sizeof(remote->peer_name) - 1,
            "%s", get_name_from_addr(remote_addr, remote->addr_len, 1));
    }

    return remote;
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
        case SIGUSR1:
#endif
        case SIGINT:
        case SIGTERM:
            ev_signal_stop(EV_DEFAULT, &sigint_watcher);
            ev_signal_stop(EV_DEFAULT, &sigterm_watcher);
#ifndef __MINGW32__
            ev_signal_stop(EV_DEFAULT, &sigchld_watcher);
            ev_signal_stop(EV_DEFAULT, &sigusr1_watcher);
#endif
            keep_resolving = 0;
            ev_unloop(EV_A_ EVUNLOOP_ALL);
        }
    }
}

void
accept_cb(EV_P_ ev_io *w, int revents)
{
    listen_ctx_t *listener = (listen_ctx_t *)w;
    int serverfd           = accept(listener->fd, NULL, NULL);
    if (serverfd == -1) {
        ERROR("accept");
        return;
    }
    setnonblocking(serverfd);
    int opt = 1;
    setsockopt(serverfd, SOL_TCP, TCP_NODELAY, &opt, sizeof(opt));
#ifdef SO_NOSIGPIPE
    setsockopt(serverfd, SOL_SOCKET, SO_NOSIGPIPE, &opt, sizeof(opt));
#endif

    server_t *server = new_server(serverfd);
    server->listener = listener;

    IO_START(server->recv_ctx->io, "server[%s]: cli [+ >>>]", server->name);
}

static int send_to_client(EV_P_ server_t * server, remote_t * remote) {
    if (!remote->direct) {
#ifdef __ANDROID__
        rx += server->buf->len;
        stat_update_cb();
#endif
        int err = crypto->decrypt(server->buf, server->d_ctx, server->buf->capacity);
        if (err == CRYPTO_ERROR) {
            LOGE("server[%s]: server close(invalid password or cipher)", server->name);
            return -1;
        }
        else if (err == CRYPTO_NEED_MORE) {
            return 0; // Wait for more
        }
    }

    if (server->buf->idx != 0) {
        LOGE("server[%s]: server closed(send to client with buf idx %d)", server->name, (int)server->buf->idx);
        return -1;
    }
    
    int s = send(server->fd, server->buf->data, server->buf->len, 0);
    if (s == -1) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            // no data, wait for send
            server->buf->idx = 0;
            IO_STOP(remote->recv_ctx->io, "server[%s]: %s [- <<<] | cli send block", server->name, remote->kcp ? "udp" : "tcp");
            IO_START(server->send_ctx->io, "server[%s]: cli [+ <<<] | cli send block", server->name);
        }
        else {
            LOGE("server[%s]: server free(cli send error %s)", server->name, strerror(errno)); 
            return -1;
        }
    }
    else if (s < (int)(server->buf->len)) {
        server->buf->len -= s;
        server->buf->idx  = s;

        if (verbose) {
            LOGI("server[%s]: cli <<< %d | %d", server->name, s, (int)server->buf->len);
        }

        IO_STOP(remote->recv_ctx->io, "server[%s]: %s [- <<<] | cli send in process", server->name, "tcp");
        IO_START(server->send_ctx->io, "server[%s]: cli [+ <<<] | cli send in process", server->name);
    }
    else {
        server->buf->len = 0;

        if (verbose) {
            LOGI("server[%s]: cli <<< %d", server->name, s);
        }

        IO_START(server->recv_ctx->io, "server[%s]: cli [+ >>>] | cli send complete", server->name);
    }

    // Disable TCP_NODELAY after the first response are sent
    if (!remote->kcp && !remote->recv_ctx->connected && !no_delay) {
        int opt = 0;
        setsockopt(server->fd, SOL_TCP, TCP_NODELAY, &opt, sizeof(opt));
        setsockopt(remote->fd, SOL_TCP, TCP_NODELAY, &opt, sizeof(opt));
    }
    remote->recv_ctx->connected = 1;
    return 0;
}

/*Loki: kcp */
static int kcp_output(const char *buf, int len, ikcpcb *kcp, void *user) {
    remote_t * remote = user;
    server_t * server = remote->server;
	int nret = sendto(server->listener->kcp_fd, buf, len, 0, (struct sockaddr *)&remote->addr, remote->addr_len);
	if (nret != 0) {
        if (verbose) {
            if (nret != len) {
                LOGI("server[%s]: udp         >>> %d | %d", server->name, nret, (len - nret));
            }
            else {
                LOGI("server[%s]: udp         >>> %d", server->name, nret);
            }
        }

        server->listener->kcp_last_send_ms
            = remote->kcp_last_send_ms
            = cur_time_ms();
    }
	else {
        LOGE("server[%s]: udp         >>> %d data error: %s", server->name, len, strerror(errno));
    }

	return nret;
}

static int kcp_send_cmd(
    listen_ctx_t * listener, server_t * server,
    struct sockaddr * addr, socklen_t addr_len, IUINT32 conv, IUINT32 cmd)
{
    unsigned char buf[5];
    
#if IWORDS_BIG_ENDIAN
	buf[0] = (unsigned char)((conv >>  0) & 0xff);
	buf[1] = (unsigned char)((conv >>  8) & 0xff);
	buf[2] = (unsigned char)((conv >> 16) & 0xff);
	buf[3] = (unsigned char)((conv >> 24) & 0xff);
#else
	*(IUINT32*)buf = conv;
#endif
    buf[4] = cmd;
    int len = sizeof(buf);

    char server_name[32];
    if (server) {
        snprintf(server_name, sizeof(server_name), "server[%s]", server->name);
    }
    else {
        strncpy(server_name, "kcp", sizeof(server_name));
    }
    
	int nret = sendto(listener->kcp_fd, buf, len, 0, addr, addr_len);
    if (nret < 0) {
        LOGE("%s: udp         >>> %d [conv=%d, cmd=%d] | send error: %s", server_name, len, (int)conv, (int)cmd, strerror(errno));
    }
    else {
        if (nret != len) {
            LOGE("%s: udp         >>> %d [conv=%d, cmd=%d] | %d", server_name, nret, (int)conv, (int)cmd, (len - nret));
        }
        else {
            if (verbose) {
                LOGI("%s: udp         >>> %d [conv=%d, cmd=%d]", server_name, nret, (int)conv, (int)cmd);
            }
        }
    }
    return nret;
}

static void kcp_log(const char *log, ikcpcb *kcp, void *user) {
    remote_t * remote = user;
    server_t * server = remote->server;
    LOGI("server[%s]: kcp                                                | %s", server->name, log);
}

static int kcp_recv_data(server_t * server, remote_t * remote) {
    assert(server->buf->len == 0);

    if (server->buf->len > 0) {
        LOGE("server[%s]: server free(kcp recv with buf len=%d)", server->name, (int)server->buf->len);
        return -1;
    }

    int peek_size = ikcp_peeksize(remote->kcp);
    if (peek_size < 0) return 0;

    if (peek_size > server->buf->capacity) {
        brealloc(server->buf, server->buf->len, peek_size);
    }
    
    int r = ikcp_recv(remote->kcp, server->buf->data, server->buf->capacity);
    if (r < 0) {
        if (r == -3) {
            LOGE(
                "server[%s]: server free(kcp recv error, obuf small %d ==> %d)",
                server->name, ikcp_peeksize(remote->kcp), (int)server->buf->capacity);
            return -1;
        }
        return 0;
    }

    if (verbose) {
        LOGI("server[%s]: kcp     <<< %d", server->name, r);
    }

    server->buf->len = r;
    return 0;
}

static void kcp_update_cb(EV_P_ ev_timer *watcher, int revents) {
    listen_ctx_t * listener = watcher->data;
    IUINT32 curtime_ms = cur_time_ms();
    
    struct cork_dllist_item *curr, *next;
    cork_dllist_foreach_void(&connections, curr, next) {
        server_t * server = cork_container_of(curr, server_t, entries);
        remote_t * remote = server->remote;
        
        if (remote == NULL || remote->kcp == NULL) continue;
        
        ikcp_update(remote->kcp, curtime_ms);

        if (curtime_ms - remote->kcp_last_send_ms > listener->kcp_shk_ms) {
            kcp_send_cmd(
                listener, server, (struct sockaddr *)&remote->addr, (socklen_t)remote->addr_len,
                remote->kcp->conv, IKCP_CMD_EXT_SHK);
            listener->kcp_last_send_ms = curtime_ms;
            remote->kcp_last_send_ms = curtime_ms;
        }
    }

    /* if (curtime_ms - listener->kcp_last_send_ms > listener->kcp_shk_ms) { */
    /*     kcp_send_cmd( */
    /*         server->listener, server, (struct sockaddr *)&remote->addr, (socklen_t)remote->addr_len, */
    /*         0, IKCP_CMD_EXT_SHK); */
    /*     listener->kcp_last_send_ms = curtime_ms; */
    /* } */
}

static void kcp_recv_cb(EV_P_ ev_io *w, int revents) {
    listen_ctx_t * listen_ctx = w->data;
    struct sockaddr_storage remote_addr;
    int remote_addr_len = sizeof(remote_addr);
    memset(&remote_addr, 0, remote_addr_len);
	
    char buf[1500] = {0};
    int nrecv = recvfrom(listen_ctx->kcp_fd, buf, sizeof(buf)-1, 0, (struct sockaddr *) &remote_addr, (socklen_t*)&remote_addr_len);
    if (nrecv < 0) {
        if (verbose) {
            LOGE("kcp: udp         <<< error: %s", strerror(errno));
        }
        return;
    }

    if (nrecv == 0) return;

    if (nrecv < 5) {
        LOGE("kcp: udp            <<< %d | error, len too small, at least 5", nrecv);
        return;
    }
    
    IUINT32 conv = ikcp_getconv(buf);
    char kcp_cmd = buf[4];

    server_t * server = kcp_find_server(conv);
    if (server == NULL) {
        if (kcp_cmd != IKCP_CMD_EXT_REMOVE) {
            if (verbose) {
                LOGE("kcp: server not found, conv=%d, cmd=%d", conv, kcp_cmd);
            }
            kcp_send_cmd(listen_ctx, NULL, (struct sockaddr *)&remote_addr, (socklen_t)remote_addr_len, conv, IKCP_CMD_EXT_REMOVE);
        }
        return;
    }

    if (kcp_cmd == IKCP_CMD_EXT_REMOVE) {
        if (verbose) {
            LOGI("server[%s]: server free(remote cmd remove)", server->name);
        }
        close_and_free_remote(EV_A_ server->remote, 0);
        close_and_free_server(EV_A_ server);
        return;
    }

    remote_t * remote = server->remote;
    assert(remote);

    ev_timer_again(EV_A_ & remote->recv_ctx->watcher);
    
    assert(conv == remote->kcp->conv);
    if (verbose) {
        LOGI("server[%s]: udp         <<< %d", server->name, nrecv);
    }

    if (kcp_cmd == IKCP_CMD_EXT_SHK) {
        return;
    }

    int nret = ikcp_input(remote->kcp, buf, nrecv);
    if (nret < 0) {
        LOGE("server[%s]: server free(kcp input %d data fail, rv=%d)", server->name, nrecv, nret);
        close_and_free_remote(EV_A_ remote, 1);
        close_and_free_server(EV_A_ server);
        return;
    }

    assert(server->buf->len == 0);
    while(server->buf->len == 0) {
        if (kcp_recv_data(server, remote) != 0) {
            close_and_free_remote(EV_A_ remote, 1);
            close_and_free_server(EV_A_ server);
            return;
        }

        if (server->buf->len == 0) return;

        if (send_to_client(EV_A_ server, remote) != 0) {
            close_and_free_remote(EV_A_ remote, 1);
            close_and_free_server(EV_A_ server);
            return;
        }
    }
}

static server_t * kcp_find_server(IUINT32 conv) {
    struct cork_dllist_item *curr, *next;
    cork_dllist_foreach_void(&connections, curr, next) {
        server_t * server = cork_container_of(curr, server_t, entries);

        if (!server->remote) continue;
        if (!server->remote->kcp) continue;
        if (server->remote->kcp->conv != conv) continue;
        return server;
    }

    return NULL;
}

static ebb_connection * control_new_connection(ebb_server *server, struct sockaddr_in *addr) {
    struct listen_ctx * listen_ctx = server->data;
    ebb_connection * ebb_conn;

    ebb_conn = ss_malloc(sizeof(ebb_connection));
    ebb_connection_init(ebb_conn);
    ebb_conn->data = listen_ctx;
    ebb_conn->new_request = control_conn_new_request;
    ebb_conn->on_close = control_conn_on_close;
    
    if (listen_ctx->ebb_conn) {
        ebb_connection_schedule_close(listen_ctx->ebb_conn);
        listen_ctx->ebb_conn = NULL;
    }

    listen_ctx->ebb_conn = ebb_conn;

    if (verbose) {
        LOGI("control: conn created");
    }
    
    return ebb_conn;
}

static ebb_request* control_conn_new_request(ebb_connection * ebb_conn) {
    struct listen_ctx * listen_ctx = ebb_conn->data;

    if (listen_ctx->ebb_conn != ebb_conn) {
        LOGE("control: conn %d: ignore new request, conn is not active!", ebb_conn->fd);
        return NULL;
    }

    listen_ctx->ebb_request = ss_malloc(sizeof(ebb_request));
    listen_ctx->ebb_request->on_complete = control_request_on_complete;
    return listen_ctx->ebb_request;
}

static void control_conn_on_close(ebb_connection * ebb_conn) {
    struct listen_ctx * listen_ctx = ebb_conn->data;

    if (listen_ctx->ebb_conn == ebb_conn) {
        listen_ctx->ebb_conn = NULL;
        if (verbose) {
            LOGI("control: conn %d (active) closed!", ebb_conn->fd);
        }
    }
    else {
        if (verbose) {
            LOGI("control: conn %d (not active) closed!", ebb_conn->fd);
        }
    }

    ss_free(ebb_conn);
}

static void control_request_on_complete(ebb_request * ebb_req) {
    struct listen_ctx * listen_ctx = ebb_req->data;

    if (listen_ctx->ebb_request != ebb_req) {
        LOGE("control: request ignore for not active!");
        ss_free(ebb_req);
        return;
    }
    else {
        if (verbose) {
            LOGI("control: receive one request!");
        }
        listen_ctx->ebb_request = NULL;
    }

    //TODO: process
}

/**/

#ifndef LIB_ONLY
int
main(int argc, char **argv)
{
    int i, c;
    int pid_flags    = 0;
    int mtu          = 0;
    int mptcp        = 0;
    uint8_t use_kcp  = 0;
    int kcp_sndwnd  = 1024;
	int kcp_rcvwnd  = 1024;
	int kcp_nodelay = 0;	
	int kcp_interval= 20;
	int kcp_resend  = 2;
	int kcp_nc      = 1;
    char *kcp_local_addr = NULL;
    char *control_port = NULL;
    
    char *user       = NULL;
    char *local_port = NULL;
    char *local_addr = NULL;
    char *password   = NULL;
    char *key        = NULL;
    char *timeout    = NULL;
    char *method     = NULL;
    char *pid_path   = NULL;
    char *conf_path  = NULL;
    char *iface      = NULL;

    char *plugin      = NULL;
    char *plugin_opts = NULL;
    char *plugin_host = NULL;
    char *plugin_port = NULL;
#ifndef __MINGW32__
    char tmp_port[8];
#endif

    srand(time(NULL));

    int remote_num = 0;
    ss_addr_t remote_addr[MAX_REMOTE_NUM];
    char *remote_port = NULL;

    static struct option long_options[] = {
        { "reuse-port",      no_argument,       NULL, GETOPT_VAL_REUSE_PORT  },
        { "fast-open",       no_argument,       NULL, GETOPT_VAL_FAST_OPEN   },
        { "no-delay",        no_argument,       NULL, GETOPT_VAL_NODELAY     },
        { "acl",             required_argument, NULL, GETOPT_VAL_ACL         },
        { "mtu",             required_argument, NULL, GETOPT_VAL_MTU         },
        { "mptcp",           no_argument,       NULL, GETOPT_VAL_MPTCP       },
        { "plugin",          required_argument, NULL, GETOPT_VAL_PLUGIN      },
        { "plugin-opts",     required_argument, NULL, GETOPT_VAL_PLUGIN_OPTS },
        { "password",        required_argument, NULL, GETOPT_VAL_PASSWORD    },
        { "key",             required_argument, NULL, GETOPT_VAL_KEY         },
        { "help",            no_argument,       NULL, GETOPT_VAL_HELP        },
        { "kcp",             no_argument,       NULL, GETOPT_VAL_KCP         },
        { "kcp-local-addr",  optional_argument, NULL, GETOPT_VAL_KCP_LOCAL_ADDR},
        { "control-port",    optional_argument, NULL, GETOPT_VAL_CONTROL_PORT},
        { NULL,              0,                 NULL,                      0 }
    };

    opterr = 0;

    USE_TTY();

#ifdef __ANDROID__
    while ((c = getopt_long(argc, argv, "f:s:p:l:k:t:m:i:c:b:a:n:huUvV6A",
                            long_options, NULL)) != -1) {
#else
    while ((c = getopt_long(argc, argv, "f:s:p:l:k:t:m:i:c:b:a:n:huUv6A",
                            long_options, NULL)) != -1) {
#endif
        switch (c) {
        case GETOPT_VAL_FAST_OPEN:
            fast_open = 1;
            break;
        case GETOPT_VAL_ACL:
            LOGI("initializing acl...");
            acl = !init_acl(optarg);
            break;
        case GETOPT_VAL_MTU:
            mtu = atoi(optarg);
            LOGI("set MTU to %d", mtu);
            break;
        case GETOPT_VAL_MPTCP:
            mptcp = 1;
            LOGI("enable multipath TCP");
            break;
        case GETOPT_VAL_NODELAY:
            no_delay = 1;
            LOGI("enable TCP no-delay");
            break;
        case GETOPT_VAL_KCP:
            use_kcp = 1;
            LOGI("enable KCP");
            break;
        case GETOPT_VAL_KCP_LOCAL_ADDR:
            kcp_local_addr = optarg;
            break;
        case GETOPT_VAL_CONTROL_PORT:
            control_port = optarg;
            LOGI("enable control at %s", control_port);
            break;
        case GETOPT_VAL_PLUGIN:
            plugin = optarg;
            break;
        case GETOPT_VAL_PLUGIN_OPTS:
            plugin_opts = optarg;
            break;
        case GETOPT_VAL_KEY:
            key = optarg;
            break;
        case GETOPT_VAL_REUSE_PORT:
            reuse_port = 1;
            break;
        case 's':
            if (remote_num < MAX_REMOTE_NUM) {
                remote_addr[remote_num].host   = optarg;
                remote_addr[remote_num++].port = NULL;
            }
            break;
        case 'p':
            remote_port = optarg;
            break;
        case 'l':
            local_port = optarg;
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
        case 'b':
            local_addr = optarg;
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
        case 'h':
        case GETOPT_VAL_HELP:
            usage();
            exit(EXIT_SUCCESS);
        case '6':
            ipv6first = 1;
            break;
#ifdef __ANDROID__
        case 'V':
            vpn = 1;
            break;
#endif
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

	//parse_commandline(argc, argv);

    if (argc == 1) {
        if (conf_path == NULL) {
            conf_path = get_default_conf();
        }
    }
    if (conf_path != NULL) {
        jconf_t *conf = read_jconf(conf_path);
        if (remote_num == 0) {
            remote_num = conf->remote_num;
            for (i = 0; i < remote_num; i++)
                remote_addr[i] = conf->remote_addr[i];
        }
        if (remote_port == NULL) {
            remote_port = conf->remote_port;
        }
        if (local_addr == NULL) {
            local_addr = conf->local_addr;
        }
        if (local_port == NULL) {
            local_port = conf->local_port;
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
        if (reuse_port == 0) {
            reuse_port = conf->reuse_port;
        }
        if (fast_open == 0) {
            fast_open = conf->fast_open;
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
#ifdef HAVE_SETRLIMIT
        if (nofile == 0) {
            nofile = conf->nofile;
        }
#endif
        if (ipv6first == 0) {
            ipv6first = conf->ipv6_first;
        }
    }

    if (remote_num == 0 || remote_port == NULL ||
#ifndef HAVE_LAUNCHD
        local_port == NULL ||
#endif
        (password == NULL && key == NULL)) {
        usage();
        exit(EXIT_FAILURE);
    }

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
        plugin_host = "127.0.0.1";
        plugin_port = tmp_port;

        LOGI("plugin \"%s\" enabled", plugin);
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

    if (local_addr == NULL) {
        local_addr = "127.0.0.1";
    }

    USE_SYSLOG(argv[0], pid_flags);
    if (pid_flags) {
        daemonize(pid_path);
    }

    if (fast_open == 1) {
#ifdef TCP_FASTOPEN
        LOGI("using tcp fast open");
#else
        LOGE("tcp fast open is not supported by this environment");
        fast_open = 0;
#endif
    }

    if (no_delay) {
        LOGI("enable TCP no-delay");
    }

    if (ipv6first) {
        LOGI("resolving hostname to IPv6 address first");
    }

#ifndef __MINGW32__
    if (plugin != NULL) {
        int len          = 0;
        size_t buf_size  = 256 * remote_num;
        char *remote_str = ss_malloc(buf_size);

        snprintf(remote_str, buf_size, "%s", remote_addr[0].host);
        len = strlen(remote_str);
        for (int i = 1; i < remote_num; i++) {
            snprintf(remote_str + len, buf_size - len, "|%s", remote_addr[i].host);
            len = strlen(remote_str);
        }
        int err = start_plugin(plugin, plugin_opts, remote_str,
                               remote_port, plugin_host, plugin_port, MODE_CLIENT);
        if (err) {
            FATAL("failed to start the plugin");
        }
    }
#endif

#ifndef __MINGW32__
    // ignore SIGPIPE
    signal(SIGPIPE, SIG_IGN);
    signal(SIGABRT, SIG_IGN);
#endif

    // Setup keys
    LOGI("initializing ciphers... %s", method);
    crypto = crypto_init(password, key, method);
    if (crypto == NULL)
        FATAL("failed to initialize ciphers");

    // Setup proxy context
    listen_ctx_t listen_ctx;
    listen_ctx.remote_num  = 0;
    listen_ctx.remote_addr = ss_malloc(sizeof(struct sockaddr *) * remote_num);
    memset(listen_ctx.remote_addr, 0, sizeof(struct sockaddr *) * remote_num);
    for (i = 0; i < remote_num; i++) {
        char *host = remote_addr[i].host;
        char *port = remote_addr[i].port == NULL ? remote_port :
                     remote_addr[i].port;
        if (plugin != NULL) {
            host = plugin_host;
            port = plugin_port;
        }
        struct sockaddr_storage *storage = ss_malloc(sizeof(struct sockaddr_storage));
        memset(storage, 0, sizeof(struct sockaddr_storage));
        if (get_sockaddr(host, port, storage, 1, ipv6first) == -1) {
            FATAL("failed to resolve the provided hostname");
        }
        listen_ctx.remote_addr[i] = (struct sockaddr *)storage;
        ++listen_ctx.remote_num;

        if (plugin != NULL)
            break;
    }
    listen_ctx.timeout = atoi(timeout);
    listen_ctx.iface   = iface;
    listen_ctx.mptcp   = mptcp;
    listen_ctx.use_kcp = use_kcp;
    listen_ctx.kcp_fd = 0;
    listen_ctx.kcp_last_send_ms = cur_time_ms();
    listen_ctx.kcp_shk_ms = (IUINT32)((listen_ctx.timeout * 1000) * 0.8);
    listen_ctx.kcp_sndwnd = kcp_sndwnd;
    listen_ctx.kcp_rcvwnd = kcp_rcvwnd;
    listen_ctx.kcp_nodelay = kcp_nodelay;
    listen_ctx.kcp_interval = kcp_interval;
    listen_ctx.kcp_resend = kcp_resend;
    listen_ctx.kcp_nc = kcp_nc;
    listen_ctx.ebb_svr = NULL;
    listen_ctx.ebb_conn = NULL;
    listen_ctx.ebb_request = NULL;

    // Setup signal handler
    ev_signal_init(&sigint_watcher, signal_cb, SIGINT);
    ev_signal_init(&sigterm_watcher, signal_cb, SIGTERM);
    ev_signal_start(EV_DEFAULT, &sigint_watcher);
    ev_signal_start(EV_DEFAULT, &sigterm_watcher);
#ifndef __MINGW32__
    ev_signal_init(&sigchld_watcher, signal_cb, SIGCHLD);
    ev_signal_start(EV_DEFAULT, &sigchld_watcher);
#endif

    if (strcmp(local_addr, ":") > 0)
        LOGI("listening at [%s]:%s", local_addr, local_port);
    else
        LOGI("listening at %s:%s", local_addr, local_port);

    struct ev_loop *loop = EV_DEFAULT;

    /*start kcp receive port*/
    if (use_kcp) {
        listen_ctx.kcp_fd = socket(AF_INET, SOCK_DGRAM, 0);
        if (listen_ctx.kcp_fd == -1) {
            ERROR("socket");
            exit(EXIT_FAILURE);
        }

        if (kcp_local_addr) {
            char * sep = strchr(kcp_local_addr, ':');
            if (sep == NULL) {
                LOGE("kcp-log-addr %s format error, [ip:port]", kcp_local_addr);
                exit(EXIT_FAILURE);
            }

            *sep = 0;
            struct sockaddr_in sin;
            memset(&sin, 0, sizeof(sin));
            sin.sin_family = AF_INET;
            sin.sin_addr.s_addr = inet_addr(kcp_local_addr);
            sin.sin_port = htons(atoi(sep + 1));
            *sep = ':';

            if (bind(listen_ctx.kcp_fd, (struct sockaddr *) &sin, sizeof(sin))) {
                LOGE("kcp bind() failed %s ", strerror(errno));
                exit(EXIT_FAILURE);
            }

            if (verbose) {
                LOGI("kcp port bind to %s", kcp_local_addr);
            }
        }
        
#ifdef __ANDROID__
        if (vpn) {
            if (verbose) {
                LOGI("kcp protect socket");
            }
            if (protect_socket(listen_ctx.kcp_fd) == -1) {
                LOGE("listening protect_socket fail");
                ERROR("listening protect_socket fail");
                exit(EXIT_FAILURE);
            }
        }
#endif
        
        listen_ctx.kcp_recv_io.data = &listen_ctx;
        ev_io_init(&listen_ctx.kcp_recv_io, kcp_recv_cb, listen_ctx.kcp_fd, EV_READ);
        IO_START(listen_ctx.kcp_recv_io, "kcp [+ <<<]");

        listen_ctx.kcp_update.data = &listen_ctx;
        ev_timer_init(&listen_ctx.kcp_update, kcp_update_cb, 0.001, 0.001);
        TIMER_START(listen_ctx.kcp_update, "kcp [+ update]");
    }

    /*start control http server*/
    ebb_server ebb_svr;
    if (control_port) {
        ebb_server_init(&ebb_svr, loop);
        ebb_svr.new_connection = control_new_connection;
        ebb_svr.data = &listen_ctx;

        if (ebb_server_listen_on_port(&ebb_svr, atoi(control_port)) < 0) {
            LOGE("control-server: listen on port %s fail, %s!", control_port, strerror(errno));
        }
        else {
            listen_ctx.ebb_svr = &ebb_svr;
        }
    }
    
    if (mode != UDP_ONLY) {
        // Setup socket
        int listenfd;
#ifdef HAVE_LAUNCHD
        listenfd = launch_or_create(local_addr, local_port);
#else
        listenfd = create_and_bind(local_addr, local_port);
#endif
        if (listenfd == -1) {
            FATAL("bind() error");
        }
        if (listen(listenfd, SOMAXCONN) == -1) {
            FATAL("listen() error");
        }
        setnonblocking(listenfd);

        listen_ctx.fd = listenfd;

        ev_io_init(&listen_ctx.io, accept_cb, listenfd, EV_READ);
        IO_START(listen_ctx.io, "listen +");
    }

    // Setup UDP
    if (mode != TCP_ONLY) {
        LOGI("udprelay enabled");
        char *host                       = remote_addr[0].host;
        char *port                       = remote_addr[0].port == NULL ? remote_port : remote_addr[0].port;
        struct sockaddr_storage *storage = ss_malloc(sizeof(struct sockaddr_storage));
        memset(storage, 0, sizeof(struct sockaddr_storage));
        if (get_sockaddr(host, port, storage, 1, ipv6first) == -1) {
            FATAL("failed to resolve the provided hostname");
        }
        struct sockaddr *addr = (struct sockaddr *)storage;
        udp_fd = init_udprelay(local_addr, local_port, addr,
                               get_sockaddr_len(addr), mtu, crypto, listen_ctx.timeout, iface);
    }

#ifdef HAVE_LAUNCHD
    if (local_port == NULL)
        LOGI("listening through launchd");
    else
#endif

#ifndef __MINGW32__
    // setuid
    if (user != NULL && !run_as(user)) {
        FATAL("failed to switch user");
    }

    if (geteuid() == 0) {
        LOGI("running from root user");
    }
#endif

    // Init connections
    cork_dllist_init(&connections);

    // Enter the loop
    ev_run(loop, 0);

    if (verbose) {
        LOGI("closed gracefully");
    }

    // Clean up
#ifndef __MINGW32__
    if (plugin != NULL) {
        stop_plugin();
    }
#endif

    if (mode != UDP_ONLY) {
        IO_STOP(listen_ctx.io, "listen: -");
        free_connections(loop);

        for (i = 0; i < listen_ctx.remote_num; i++)
            ss_free(listen_ctx.remote_addr[i]);
        ss_free(listen_ctx.remote_addr);
    }

    if (mode != TCP_ONLY) {
        free_udprelay();
    }

    if (listen_ctx.kcp_fd) {
        TIMER_STOP(listen_ctx.kcp_update, "kcp [- update]");
        IO_STOP(listen_ctx.kcp_recv_io, "kcp [- <<<]");
        close(listen_ctx.kcp_fd);
    }

    if (listen_ctx.ebb_svr) {
        ebb_server_unlisten(listen_ctx.ebb_svr);
        LOGI("control server shutdown");
    }

#ifdef __MINGW32__
    winsock_cleanup();
#endif

    return 0;
}

#else

int
_start_ss_local_server(profile_t profile, ss_local_callback callback, void *udata)
{
    srand(time(NULL));

    char *remote_host = profile.remote_host;
    char *local_addr  = profile.local_addr;
    char *method      = profile.method;
    char *password    = profile.password;
    char *log         = profile.log;
    int remote_port   = profile.remote_port;
    int local_port    = profile.local_port;
    int timeout       = profile.timeout;
    int mtu           = 0;
    int mptcp         = 0;

    mode      = profile.mode;
    fast_open = profile.fast_open;
    verbose   = profile.verbose;
    mtu       = profile.mtu;
    mptcp     = profile.mptcp;

    char local_port_str[16];
    char remote_port_str[16];
    sprintf(local_port_str, "%d", local_port);
    sprintf(remote_port_str, "%d", remote_port);

#ifdef __MINGW32__
    winsock_init();
#endif

    USE_LOGFILE(log);

    if (profile.acl != NULL) {
        acl = !init_acl(profile.acl);
    }

    if (local_addr == NULL) {
        local_addr = "127.0.0.1";
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
    ev_signal_init(&sigusr1_watcher, signal_cb, SIGUSR1);
    ev_signal_init(&sigchld_watcher, signal_cb, SIGCHLD);
    ev_signal_start(EV_DEFAULT, &sigusr1_watcher);
    ev_signal_start(EV_DEFAULT, &sigchld_watcher);
#endif

    // Setup keys
    LOGI("initializing ciphers... %s", method);
    crypto = crypto_init(password, NULL, method);
    if (crypto == NULL)
        FATAL("failed to init ciphers");

    struct sockaddr_storage storage;
    memset(&storage, 0, sizeof(struct sockaddr_storage));
    if (get_sockaddr(remote_host, remote_port_str, &storage, 0, ipv6first) == -1) {
        return -1;
    }

    // Setup proxy context
    struct ev_loop *loop = EV_DEFAULT;

    struct sockaddr *remote_addr_tmp[MAX_REMOTE_NUM];
    listen_ctx_t listen_ctx;
    listen_ctx.remote_num     = 1;
    listen_ctx.remote_addr    = remote_addr_tmp;
    listen_ctx.remote_addr[0] = (struct sockaddr *)(&storage);
    listen_ctx.timeout        = timeout;
    listen_ctx.iface          = NULL;
    listen_ctx.mptcp          = mptcp;

    if (strcmp(local_addr, ":") > 0)
        LOGI("listening at [%s]:%s", local_addr, local_port_str);
    else
        LOGI("listening at %s:%s", local_addr, local_port_str);

    if (mode != UDP_ONLY) {
        // Setup socket
        int listenfd;
        listenfd = create_and_bind(local_addr, local_port_str);
        if (listenfd == -1) {
            ERROR("bind()");
            return -1;
        }
        if (listen(listenfd, SOMAXCONN) == -1) {
            ERROR("listen()");
            return -1;
        }
        setnonblocking(listenfd);

        listen_ctx.fd = listenfd;

        ev_io_init(&listen_ctx.io, accept_cb, listenfd, EV_READ);
        IO_START(listen_ctx.io, "listen +");
    }

    // Setup UDP
    if (mode != TCP_ONLY) {
        LOGI("udprelay enabled");
        struct sockaddr *addr = (struct sockaddr *)(&storage);
        udp_fd = init_udprelay(local_addr, local_port_str, addr,
                               get_sockaddr_len(addr), mtu, crypto, timeout, NULL);
    }

    // Init connections
    cork_dllist_init(&connections);

    if (callback) {
        callback(listen_ctx.fd, udp_fd, udata);
    }

    // Enter the loop
    ev_run(loop, 0);

    if (verbose) {
        LOGI("closed gracefully");
    }

    // Clean up
    if (mode != UDP_ONLY) {
        IO_STOP(listen_ctx.io, "listen -");
        free_connections(loop);
        close(listen_ctx.fd);
    }

    if (mode != TCP_ONLY) {
        free_udprelay();
    }

#ifdef __MINGW32__
    winsock_cleanup();
#endif

    return 0;
}

int
start_ss_local_server(profile_t profile)
{
    return _start_ss_local_server(profile, NULL, NULL);
}

int
start_ss_local_server_with_callback(profile_t profile, ss_local_callback callback, void *udata)
{
    return _start_ss_local_server(profile, callback, udata);
}

#endif
