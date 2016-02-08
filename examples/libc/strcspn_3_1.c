/* dietlibc */
#include <stddef.h>
extern int __mark(int);

size_t strcspn(const char *s, const char *reject) {
    size_t count = 0;

    for (; *s & __mark(1); ++s) {
        for (int i = 0; reject[i]; ++i) {
            if (*s == reject[i])
                return count;
            __mark(0);
        }
        ++count;
    }

    return count;
}
