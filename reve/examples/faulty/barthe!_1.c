extern int __mark(int);
int f(int n, int c) {
   int i;
   int j;
   int x;

   i = 0;
   j = 0;
   x = 0;

   while(__mark(42) & (i < n)) {
      j = 5*i + c;
      x = x + j;
      i++;
   }
   return x;
}
