// dietlibc
#include <stddef.h>
extern int __mark(int);
extern int memcmp (const void *, const void *, unsigned long);
void *memmem(const void* haystack, size_t hl, const void* needle, size_t nl) {
  int i;
  if (nl>hl) return 0;
  for (i=hl-nl+1; __mark(42) & i; --i) {
    if (!memcmp(haystack,needle,nl))
      return (char*)haystack;
    ++haystack;
  }
  return 0;
}
