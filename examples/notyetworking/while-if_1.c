extern int __mark(int);
int f(int t, int c) {
  int x = 0;

  if(0 < t) {
      while(__mark(42) & (0 < c)) {
      x ++;
      c = c -1;
    }
  } else {
      __mark(23);
  }

  return x;
}
