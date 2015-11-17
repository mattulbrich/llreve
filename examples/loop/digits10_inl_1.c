extern int __mark(int);
int f(int n) {
  int result = 1;
  n = n/10;

  while (__mark(42) & n > 0) {
    result++;
    n = n / 10;
    if (n > 0) {
      result++;
      n = n / 10;
      if (n > 0) {
        result++;
        n = n / 10;
        if (n > 0) {
          result++;
          n = n / 10;
        }
      }
    }
  }
  return result;
}
