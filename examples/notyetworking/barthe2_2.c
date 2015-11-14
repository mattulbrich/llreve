extern int __mark(int);
int f(int n) {
  int j = 1;
  int x = 0;
  while (__mark(1) & j <= n) {
    x = x + j;
    j++;
  }
  return x;
}
