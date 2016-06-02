extern int __mark(int);
/*@ pre (bvsle n$1_0__1 (_ bv100000000 32)) @*/
int f(int n) {
  int i = 0;
  int j = 0;

  while (__mark(42) & (i <= n)) {
    i++;
    j++;
  }
  return j;
}
