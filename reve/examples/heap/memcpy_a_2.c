extern int __mark(int);

int memcpy(int *dest, int *src, int size) {
   int *start = src;
   while(__mark(42) & (src - start < size)) {
      *dest = *src;
      dest++;
      src++;
   }
   return 1;
}
