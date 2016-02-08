/* glibc */
/*@ rel_in
   (and
      (= s$1_0 s$2_0)
      (= reject$1_0 reject$2_0)
      (> reject$1_0 0)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i))))
@*/
#include <stddef.h>
extern int __mark(int);

__attribute__((always_inline))
static char *strchr(register const char *t, int c) {
    register char ch;

    ch = c;
    for (;;) {
        if (*t == ch)
            break;
        if (!*t)
            return 0;
        ++t;
        __mark(0);
    }
    return (char *)t;
}

size_t strcspn(const char *s, const char *reject) {
    size_t count = 0;

    while (__mark(1) & (*s)) {
        char ch = *s++;
        if (strchr(reject, ch) == NULL) {
            ++count;
        } else {
            return count;
        }
    }

    return count;
}
