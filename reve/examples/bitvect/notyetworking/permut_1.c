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
    if (!x) {
      return x;
    }
    int8_t k = -1;
    for (uint8_t j = 7; __mark(1) & (j >= 1); j--) {
      if (((x >> j) & 1) < ((x >> (j - 1)) & 1)) {
        k = 7 - j;
      }
    }
    if (k == -1) {
      x = 0xff;
      return x;
    }
    int8_t l = k + 1;
    for (uint8_t j = l; __mark(2) & (j < 8); ++j) {
      if (((x >> (7 - k)) & 1) < ((x >> (7 - j)) & 1)) {
        l = j;
      }
    }
    // swap
    uint8_t valk = (x >> (7 - k)) & 1;
    uint8_t vall = (x >> (7 - l)) & 1;
    x ^= (-vall ^ x) & (1 << (7 - k));
    x ^= (-valk ^ x) & (1 << (7 - l));
    uint8_t oldx = x;
    for (uint8_t j = k + 1; __mark(3) & (j < 8); ++j) {
      uint8_t valj = (oldx >> (7 - j)) & 1;
      uint8_t index = 7 - j + k + 1;
      x ^= (-valj ^ x) & (1 << (7 - index));
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
