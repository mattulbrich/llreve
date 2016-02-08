#include <stddef.h>
// dietlibc

extern int __mark(int);
void* memchr(const void *s, int c, size_t n) {
  const unsigned char *pc = (unsigned char *) s;
  for (;n--;pc++) {
    if (*pc == c)
      return ((void *) pc);
    __mark(42);
  }
  return 0;
}
