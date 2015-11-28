extern int __mark(int);

int fib(int n,int *x) {
   int i = 2;
   int a = 1;
   int b = 1;
   int t;

   while(__mark(42) & i < n) {
      t = a;
      a = b;
      b = a+t;
      i++;
   }

   return b;
}
