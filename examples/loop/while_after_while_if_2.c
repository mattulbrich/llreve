extern int __mark(int);
int f(int t, int c, int r) {
  int x = 0;

  while(__mark(23) & __mark(42) & (0 < c)) {
      if (0 < t) {
          x++;
      }
      c--;
  }

  while(__mark(13) & (r > 0)) {
      x+=2;
      r--;
  }

  return x;
}
