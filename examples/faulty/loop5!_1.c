extern int __mark(int);
int f(int n) {
  int i;
  int j;
  i = 0;
  j = 0;
  while (__mark(42) & i < n + n) {
    j++;
    i++;
  }
  return j;
}
