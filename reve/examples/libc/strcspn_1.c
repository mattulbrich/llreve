/* openbsd */
#include <stddef.h>
extern int __mark(int);
size_t strcspn(const char *s, const char *reject) {
    const char *p, *spanp;
    char c, sc;
    for (p = s; *p & __mark(0);) {
        c = *p++;
        spanp = reject;
        do {
            if ((sc = *spanp++) == c)
                return (p - 1 - s);
        } while ((sc != 0) && __mark(1));
    }
    return 0;
}
