extern int __mark(int);
int f(int n) {
  int i = 0;
  int j = 0;

  while (i <= n) {
    __mark(42);
    i++;
    j++;
  }
  return j;
}
