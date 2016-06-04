#include <stdint.h>
#include <stdio.h>

#define BIN_PAT "%c%c%c%c%c%c%c%c"
#define TO_BIN(byte)                                                           \
  (byte & 0x80 ? '1' : '0'), (byte & 0x40 ? '1' : '0'),                        \
      (byte & 0x20 ? '1' : '0'), (byte & 0x10 ? '1' : '0'),                    \
      (byte & 0x08 ? '1' : '0'), (byte & 0x04 ? '1' : '0'),                    \
      (byte & 0x02 ? '1' : '0'), (byte & 0x01 ? '1' : '0')

extern int __mark(int);
// Finds the nth permutation of x
uint8_t f(uint8_t x) {
    for (uint8_t i = 0; __mark(1) & (i < 8); ++i) {
        if (x >> (7-i) & 1) {
            if (i == 0) {
                x = 0xff;
                break;
            } else {
                x = 1 << (7-i+1);
                break;
            }
        }
    }
  return x;
}

/* int main() { */
/*   uint8_t x = 0xAA; */
/*   for (int i = 0; i < 50; ++i) { */
/*     uint8_t result = f(x, i); */
/*     printf("%d th permutation of " BIN_PAT ": " BIN_PAT "\n", i, TO_BIN(x),
 */
/*            TO_BIN(result)); */
/*   } */
/*   x = 0x92; */
/*   printf("\n"); */
/*   for (int i = 0; i < 50; ++i) { */
/*     uint8_t result = f(x, i); */
/*     printf("%d th permutation of " BIN_PAT ": " BIN_PAT "\n", i, TO_BIN(x),
 */
/*            TO_BIN(result)); */
/*   } */
/* } */
