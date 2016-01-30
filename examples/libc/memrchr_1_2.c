/* glibc */
#include <stddef.h>
extern int __mark(int);
void *memrchr(const void *s, int c, size_t n) {
    const unsigned char *char_ptr;
    char_ptr = (unsigned char*)s + n;
    while (n-- > 0) {
        if (*--char_ptr == c)
            return (void *)char_ptr;
        __mark(0);
    }

    return 0;
}
