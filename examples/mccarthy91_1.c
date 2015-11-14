int f(int a) {
  int r;
  r = 0;
  if (a > 100) {
    r = a - 10;
  } else {
    r = f(a + 11);
    r = f(r);
  }
  return r;
}
