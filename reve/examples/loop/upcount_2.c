/*@ rel_in (and (= n$1_0 n$2_0) (>= n$1_0 0) (>= n$2_0 0))  @*/

extern int __mark(int);
int upcount(int n) {
   int m = 0;
   while(__mark(42) & (n > 0)) {
      m++;
      n--;
   }
   return m+1;
}
