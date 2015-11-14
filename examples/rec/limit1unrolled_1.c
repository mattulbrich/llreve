int f(int n) {
  int r;
  int rx;
  int nx;

  r = 0;
  rx = 0;
  nx = 0;

  if (n <= 1) {
    r = n;
  } else {
    // BEGIN INLINING
    nx = n - 1;
    rx = 0;
    if (nx <= 1) {
      rx = nx;
    } else {
      rx = f(nx - 1);
      rx = nx + rx;
    }
    r = rx;
    // END INLINING
    r = n + r;
  }

  return r;
}
