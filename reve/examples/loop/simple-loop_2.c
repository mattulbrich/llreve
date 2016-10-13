extern int __mark(int);
int f(int z) {
  int i = 1;

  while (__mark(42) & (i <= 10)) {
    i++;
  }
  return i;
}
