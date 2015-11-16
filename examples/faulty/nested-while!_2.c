extern int __mark(int);
int f(int x, int g) {
  int i;
  i = 0;
  while (__mark(42) & (i < x)) {
    i = i + 1;
    g = g - 2;
    while(__mark(23) & (x < i)) {
      x = x + 1;
      g = g + 2;
    }
  }
  return g;
}
