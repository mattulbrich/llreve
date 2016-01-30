// openbsd
#include <stddef.h>
extern int __mark(int);
void *memmove(void *dst0, const void *src0, size_t length) {
    char *dst = dst0;
    const char *src = src0;
    size_t t;

    if (length == 0 || dst == src) /* nothing to do */
        goto done;

    if ((unsigned long)dst < (unsigned long)src) {
        t = length;
        if (t) {
            do {
                *dst++ = *src++;
            } while (__mark(0) & (--t));
        }
    } else {
        src += length;
        dst += length;
        t = length;
        if (t) {
            do {
                *--dst = *--src;
            } while (__mark(1) & (--t));
        }
    }
done:
    return (dst0);
}
