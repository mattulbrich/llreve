extern int __mark(int);
int f(int n) {
  int i = n;
  int j = 0;

  while (__mark(42) & (i >= 0)) {
    i = i - 1;
    j++;
  }
  return j;
}
