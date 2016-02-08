int f(int n) {
  int r;
  r = 0;

  if (n <= 1) {
    r = n;
  } else {
    r = f(n - 3);
    r = n + (n-1) + r;
  }

  return r;
}
