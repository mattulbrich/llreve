int g(int n)
{
  int r=0;
  int i=n;

  while (i > 0) {
    r = r + n;
    i--;
  }

  i=n;
  n=r;
  r=0;
  while (i > 0) {
    r = r + n;
    i--;
  }

  return r;
}

