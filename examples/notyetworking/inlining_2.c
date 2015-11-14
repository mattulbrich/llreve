int f(int x) {
  if (x > 1) {
    x = f(x-2);
    x = x + 2;
  }
  if (x < 0) {
    x = 0;
  }
  return x;
}
