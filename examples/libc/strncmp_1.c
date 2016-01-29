/* openbsd */
/*@ rel_in
  (and
      (= s1$1_0 s1$2_0)
      (= s2$1_0 s2$2_0)
      (= n$1_0 n$2_0)
      (>= n$1_0 0)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i))))
  @*/
#include <stddef.h>

extern int __mark(int);

int strncmp(const char *s1, const char *s2, size_t n) {

    if (n == 0)
        return (0);
    do {
        if (*s1 != *s2++)
            return (*(unsigned char *)s1 - *(unsigned char *)--s2);
        if (*s1++ == 0)
            break;
    } while (__mark(42) & (--n != 0));
    return (0);
}
