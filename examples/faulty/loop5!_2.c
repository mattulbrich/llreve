extern int __mark(int);
int f(int n) {
  int i;
  int j;
  i = n + 1;
  j = 0;
  while (__mark(42) & i > 0) {
    j = j + 2;
    i = i - 1;
  }
  return j;
}
