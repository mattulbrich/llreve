/* openbsd */
#include <stddef.h>
extern int __mark(int);
void *memccpy(void *t, const void *f, int c, size_t n) {
    if (n) {
        unsigned char *tp = t;
        const unsigned char *fp = f;
        unsigned char uc = c;
        do {
            if ((*tp++ = *fp++) == uc)
                return (tp);
        } while (__mark(0) & (--n != 0));
    }
    return (0);
}
