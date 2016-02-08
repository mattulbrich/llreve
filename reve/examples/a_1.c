extern void __mark(int);

int f(int n) {
   int i;
   int sum = 0;

   for(i = 2; i <= n; i++) {
      __mark(0);
      sum += i;
   }

   return sum;
}
