extern int __mark(int);

int memcpy(int *dest, int *src, int size) {
   int i = 0;
   while(__mark(42) & (i < size)) {
      dest[i] = src[i];
      i++;
   }
   return 1;
}
