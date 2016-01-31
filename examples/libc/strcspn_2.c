/* dietlibc */
#include <stddef.h>
extern int __mark(int);
size_t strcspn(const char *s, const char *reject) {
    size_t l = 0;
    int i;
    for (; *s & __mark(0); ++s) {
        for (i = 0; reject[i]; ++i) {
            if (*s == reject[i])
                return l;
            __mark(1);
        }
        ++l;
    }
    return 0;
}
