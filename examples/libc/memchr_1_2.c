#include <stddef.h>
// openbsd
extern int __mark(int);
void *
memchr(const void *s, int c, size_t n)
{
	if (n != 0) {
		const unsigned char *p = s;

		do {
			if (*p++ == (unsigned char)c)
				return ((void *)(p - 1));
		} while (__mark(42) & (--n != 0));
	}
	return (NULL);
}
