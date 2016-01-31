/* glibc */
#include <stddef.h>
extern int __mark(int);
char *strchr(const char *s, int c_in) {
    unsigned char c;

    c = (unsigned char)c_in;

    for (;__mark(42);) {
        if (*s == c)
            return (char *)s;
        else if (*s == '\0')
            return NULL;
        if (*++s == c)
            return (char *)s;
        else if (*s == '\0')
            return NULL;
        if (*++s == c)
            return (char *)s;
        else if (*s == '\0')
            return NULL;
        if (*++s == c)
            return (char *)s;
        else if (*s == '\0')
            return NULL;
    }
    return NULL;
}
