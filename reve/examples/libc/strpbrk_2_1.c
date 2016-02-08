/* glibc */
#include <stddef.h>
extern int __mark(int);
char *strpbrk(const char *s, const char *accept) {
    while (__mark(0) & (*s != '\0')) {
        const char *a = accept;
        while (__mark(1) & (*a != '\0'))
            if (*a++ == *s)
                return (char *)s;
        ++s;
    }

    return NULL;
}
