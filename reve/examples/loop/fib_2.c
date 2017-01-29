/*@ rel_in (= n$1 (+ n$2 1)) @*/
extern int __mark(int);
int fib(int n) {
  int f = 1;  //  <---- starting at 1
  int g = 1;
  int h = 0;

  while(__mark(42) & (n > 0)) {
    h = f + g;
    f = g;
    g = h;
    n --;
  }

  return g;
}
