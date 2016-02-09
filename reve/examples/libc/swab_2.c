/* openbsd */
/*@ rel_in
(and
      (= src$1_0 from$2_0)
      (= dest$1_0 to$2_0)
      (= nbytes$1_0 len$2_0)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))
; no overlap
      (<= (+ src$1_0 nbytes$1_0) dest$1_0))
@*/
#include <unistd.h>
extern int __mark(int);
void swab(const void *from, void *to, ssize_t len) {
    const unsigned char *src = from;
    unsigned char *dst = to;
    unsigned char t0, t1;

    while (__mark(0) & (len > 1)) {
        t0 = src[0];
        t1 = src[1];
        dst[0] = t1;
        dst[1] = t0;
        src += 2;
        dst += 2;
        len -= 2;
    }
}
