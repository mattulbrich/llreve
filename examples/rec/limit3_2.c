int f(int n) {
  int r;
  r = 0;

  if (n <= 1) {
    r = n;
  } else {
    r = f(n - 1);
    if (r >= 0) {
      r = n + r;
    }
  }

  return r;
}
