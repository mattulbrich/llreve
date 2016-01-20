/*@ pre 0<=n && n<=1 @*/
int g(int n)
{
  int r=0;
  int i=n;

  while (i > 0) {
    r = r + n;
    i--;
  }

  return r;
}

