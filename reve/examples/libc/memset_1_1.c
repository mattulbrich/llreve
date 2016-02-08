/* openbsd */
#include <stddef.h>
extern int __mark(int);

void *
memset(void *dst, int c, size_t n)
{
	if (n != 0) {
		unsigned char *d = dst;

		do
			*d++ = (unsigned char)c;
		while (__mark(0) & (--n != 0));
	}
	return (dst);
}
