extern int __mark(int);

void memcpy(int *dest, int *src, int size) {
   src--;
   dest--;

   while(__mark(42) & (size > 0)) {
      dest++;
      src++;
      *dest = *src;
      size--;
   }
}
