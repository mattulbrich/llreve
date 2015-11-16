extern int __mark(int);
int f(int n, int c) {
   int i;
   int j;
   int x;

   i = 0;
   j = c;
   x = 0;

   while(__mark(42) & i < n) {
      x = x + j;
      j = j + 5;
      if (i == 10) {
        j = 10;
      }
      i++;
   }
   return x;
}
