/* dietlibc */
#include <stddef.h>
extern int __mark(int);
void *memccpy(void *dst, const void *src, int c, size_t count) {
    char *a = dst;
    const char *b = src;
    while (count--) {
        *a++ = *b;
        if (*b == c) {
            return (void *)a;
        }
        b++;
        __mark(0);
    }
    return 0;
}
