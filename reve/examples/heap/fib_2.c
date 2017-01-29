/*@ rel_in (and (= n$1 n$2) (= x$1 a$2) (= HEAP$1 HEAP$2) (>= n$1 0)) @*/
/*@ rel_out (= result$1 result$2) @*/

extern int __mark(int);
int fib(int n, int *a) {
   int i = 2;
   a[0] = 1;
   a[1] = 1;

   while(__mark(42) & (i < n)) {
      a[i] = a[i-1] + a[i-2];
      i++;
   }

   return a[i-1];
}
