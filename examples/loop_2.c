extern int __mark(int);
int f(int n) {
  int i = n;
  int j = 0;

  while (i >= 0) {
    __mark(42);
    i = i - 1;
    j++;
  }
  return j;
}
