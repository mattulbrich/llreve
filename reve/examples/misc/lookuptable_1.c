/*@ opt -strings @*/
#include <stddef.h>
/*@ rel_in
(and
      (= s1$1 s1$2)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))
      (>= (select HEAP$1 s1$1) 0)
      (< (select HEAP$1 s1$1) 255))
@*/
extern int __mark(int);

int strncasecmp(const int *s1) {
    int val = *s1;
    if (val >= 'A' && val <= 'Z') {
        return val + 'a' - 'A';
    }
    return val;
}
