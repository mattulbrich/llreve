/* openbsd */
#include <stddef.h>
extern int __mark(int);
char *strpbrk(const char *s1, const char *s2) {
    const char *scanp;
    int c, sc;

    while (__mark(0) & ((c = *s1++) != 0)) {
        for (scanp = s2; __mark(1) & ((sc = *scanp++) != 0);)
            if (sc == c)
                return ((char *)(s1 - 1));
    }
    return (NULL);
}
