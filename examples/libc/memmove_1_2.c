/* dietlibc */
#include <stddef.h>
extern int __mark(int);
void *memmove(void *dst, const void *src, size_t count) {
    char *a = dst;
    const char *b = src;
    if (src != dst) {
        if (src > dst) {
            while (count--) {
                *a++ = *b++;
                __mark(0);
            }
        } else {
            a += count - 1;
            b += count - 1;
            while (count--) {
                *a-- = *b--;
                __mark(1);
            }
        }
    }
    return dst;
}
