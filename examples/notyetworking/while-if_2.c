extern int __mark(int);
int f(int t, int c) {
  int x = 0;

  while(__mark(42) & __mark(23) & (0 < c)) {
    if(0 < t) {
      x ++;
    }
    c = c - 1;
  }

  return x;
}
