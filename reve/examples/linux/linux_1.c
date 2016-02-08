/*@ rel_in (and (= net$1_0 net$2_0) (= uaddr$1_0 uaddr$2_0) (= uaddr_len$1_0 uaddr_len$2_0) (= sap$1_0 sap$2_0) (= salen$1_0 salen$2_0) (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i))) (>= net$1_0 0) (>= uaddr$1_0 0) (>= sap$1_0 0) (>= net$2_0 0) (>= uaddr$2_0 0) (>= sap$2_0 0) (or (> uaddr_len$1_0 42) (<= uaddr_len$1_0 40))) @*/
#define RPCBIND_MAXUADDRLEN  	(42)
#define NULL 			(0)
#define unlikely(c)		(c)

typedef enum {AF_INET, AF_INET6} family;

typedef int size_t;

struct net {
};

struct sockaddr {
	family sa_family;
};

struct sockaddr_in {
	int sin_port;
};

struct sockaddr_in6 {
	int sin6_port;
};

extern int memcpy(char*, const char*, int);
extern char * strrchr(char*, int);
extern int strlen(char*);
extern int strict_strtoul(char*, int, unsigned long*);
extern int htons(int);
extern int rpc_pton(struct net*, char*, int, struct sockaddr *, int);

size_t rpc_uaddr2sockaddr(struct net *net, const char *uaddr,
		const size_t uaddr_len, struct sockaddr *sap,
		const size_t salen)
{
	char *c, buf[RPCBIND_MAXUADDRLEN];
	unsigned long portlo, porthi;
	unsigned short port = 0;
	int r = 0;

	if (uaddr_len > RPCBIND_MAXUADDRLEN) {
		r = 1;
		return 0;
	}

	memcpy(buf, uaddr, uaddr_len);

	buf[uaddr_len] = '\0';
	c = strrchr(buf, '.');

	if (unlikely(c == NULL))
		return 0;
	if (unlikely(strict_strtoul(c + 1, 10, &portlo) != 0))
		return 0;
	if (unlikely(portlo > 255))
		return 0;

	*c = '\0';
	c = strrchr(buf, '.');
	if (unlikely(c == NULL))
		return 0;
	if (unlikely(strict_strtoul(c + 1, 10, &porthi) != 0))
		return 0;
	if (unlikely(porthi > 255))
		return 0;

	*c = '\0';
	if (rpc_pton(net, buf, strlen(buf), sap, salen) == 0)
		return 0;

	if (sap->sa_family == AF_INET) {
		((struct sockaddr_in *)sap)->sin_port = htons(port);
		return sizeof(struct sockaddr_in);
	} else if (sap->sa_family == AF_INET6) {
		((struct sockaddr_in6 *)sap)->sin6_port = htons(port);
		return sizeof(struct sockaddr_in6);
	}

	return 0;
}
