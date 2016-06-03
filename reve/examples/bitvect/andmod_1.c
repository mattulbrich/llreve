#include <stdint.h>
extern int __mark(int);
uint32_t f(uint32_t x) {
    uint32_t sum = 0;
    for (uint32_t i = 0; __mark(0) & (i < x); ++i) {
        if (i & 1) {
            sum += i;
        }
    }
    return sum;
}
