#include <stdint.h>
#include <stdio.h>

#define BIN_PAT "%c%c%c%c%c%c%c%c"
#define TO_BIN(byte)                                                           \
  (byte & 0x80 ? '1' : '0'), (byte & 0x40 ? '1' : '0'),                        \
      (byte & 0x20 ? '1' : '0'), (byte & 0x10 ? '1' : '0'),                    \
      (byte & 0x08 ? '1' : '0'), (byte & 0x04 ? '1' : '0'),                    \
      (byte & 0x02 ? '1' : '0'), (byte & 0x01 ? '1' : '0')

extern int __mark(int);
extern int __splitmark(int);
// Finds the nth permutation of x
uint8_t f(uint8_t x) {
    if (!x) {
      return x;
    }
    uint8_t t = (x | (x - 1)) + 1;
    x = t | ((((t & -t) / (x & -x)) >> 1) - 1);
    __splitmark(1);
    __splitmark(2);
    __splitmark(3);

  return x;
}

/* int main() { */
/*   uint8_t x = 0xAA; */
/*   for (int i = 0; i < 50; ++i) { */
/*     printf("%d th permutation of " BIN_PAT */
/*            ": " BIN_PAT "\n", */
/*            i, TO_BIN(x), TO_BIN(f(x, i))); */
/*   } */
/*   x = 0x92; */
/*   printf("\n"); */
/*   for (int i = 0; i < 50; ++i) { */
/*     printf("%d th permutation of " BIN_PAT */
/*            ": " BIN_PAT "\n", */
/*            i, TO_BIN(x), TO_BIN(f(x, i))); */
/*   } */
/*   x = 0x00; */
/*   printf("\n"); */
/*   for (int i = 0; i < 50; ++i) { */
/*     printf("%d th permutation of " BIN_PAT */
/*            ": " BIN_PAT "\n", */
/*            i, TO_BIN(x), TO_BIN(f(x, i))); */
/*   } */
/* } */
