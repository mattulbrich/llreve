int f(int i, int j)
{
  int r;
  r = 0;

  if (i == 0) {
    r = j;
  } else {
    if (i == 1) {
      r = j + 1;
    } else { if (i == 2) {
      r = j;
    } else {
      r = f(i - 1, j + 1);
    }}
  }

  return r;
}
