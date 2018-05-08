/* openbsd */
/*@ rel_in
(and
      (= src$1 from$2)
      (= dest$1 to$2)
      (= nbytes$1 len$2)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))
; no overlap
      (<= (+ src$1 nbytes$1) dest$1))
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
