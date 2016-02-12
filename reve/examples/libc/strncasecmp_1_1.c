#include <stddef.h>
extern int __mark(int);

typedef unsigned char u_char;

int strncasecmp(const char *s1, const char *s2, size_t len) {
    register unsigned int x2 = 0;
    register unsigned int x1 = 0;
    register const char *end = s1 + len;

    while (__mark(0) & 1) {
        if (s1 >= end)
            return 0;
        x1 = *s1;
        x2 = *s2;
        if (x1 >= 'A' && x1 <= 'Z') {
            x1 += 'a' - 'A';
        }
        if (x2 >= 'A' && x2 <= 'Z') {
            x2 += 'a' - 'A';
        }
        s1++;
        s2++;
        if (x2 != x1)
            break;
        if (x1 == (unsigned int)-'A')
            break;
    }

    return x1 - x2;
}
