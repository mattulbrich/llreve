/* openbsd */
#include <stddef.h>
extern int __mark(int);
void *memrchr(const void *s, int c, size_t n) {
    const unsigned char *cp;

    if (n != 0) {
        cp = (unsigned char *)s + n;
        do {
            if (*(--cp) == (unsigned char)c)
                return ((void *)cp);
        } while (__mark(0) & (--n != 0));
    }
    return (NULL);
}
