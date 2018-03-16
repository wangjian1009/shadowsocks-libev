#ifndef	_KCP_CONFIG_
#define	_KCP_CONFIG_

struct kcp_param {
	int		sndwnd;			// sndwnd
	int		rcvwnd;			// rcvwnd
	int 	nodelay;		// nodelay
	int		interval;		// interval
	int 	resend;			// resend
	int 	nc; 			// no congestion
};

int kcp_parse_param(struct kcp_param *config, const char *filename);
int kcp_parse_json_param(struct kcp_param *config, const char *filename);

#endif
