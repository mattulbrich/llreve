extern int __mark(int);
int f(int t, int c, int r) {
  int x = 0;

  if (0 < t) {
      while(__mark(42) & (0 < c)) {
          x++;
          c--;
      }
  } else {
      __mark(23);
  }

  while(__mark(13) & r > 0) {
      x+=2;
      r--;
  }

  return x;
}
