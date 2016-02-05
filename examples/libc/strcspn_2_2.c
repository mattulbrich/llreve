/* glibc */
#include <stddef.h>
extern int __mark(int);

size_t strcspn(const char *s, const char *reject) {
    size_t count = 0;

    while (__mark(1) & (*s)) {
        char ch = *s++;
        const char *t = reject;
        for (;__mark(0);) {
            if (*t == ch)
                return count;
            if (!*t) {
                ++count;
                break;
            }
            ++t;
        }
    }

    return count;
}
