extern int __mark(int);
/*@ pre 0<=n && n<=1 @*/
int g(int n)
{
  int r=0;
  int i=n;
  __mark(0);

  while (__mark(1) & i > 0) {
    r = r + n;
    i--;
  }

  return r;
}
