extern int __mark(int);
int f(int t, int c) {
  int x = 0;

  if (0 < t) {
      while(__mark(42) & (0 < c)) {
          x++;
          c--;
      }
  } else {
      while(__mark(23) & (0 < c)) {
          x--;
          c--;
      }
  }

  return x;
}
