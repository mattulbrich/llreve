/* openbsd */
#include <unistd.h>
extern int __mark(int);
void swab(const void *from, void *to, ssize_t len) {
    const unsigned char *src = from;
    unsigned char *dst = to;
    unsigned char t0, t1;

    while (__mark(0) & (len > 1)) {
        // CHANGED: openbsd actually reads both values first, that way
        // it works correctly when from and to are equal, sadly posix
        // says that that the behavior is undefined if the two regions
        // overlap, so we can’t clam to have found a bug
        /* t0 = src[0]; */
        t1 = src[1];
        dst[0] = t1;
        // CHANGED
        t0 = src[0];
        dst[1] = t0;
        src += 2;
        dst += 2;
        len -= 2;
    }
}
