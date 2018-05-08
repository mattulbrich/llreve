/*@ rel_in (and (= n$1 n$2) (<= 0 n$1) (<= n$1 1)) @*/
extern int __mark(int);

int g(int n)
{
  int r=0;
  int i=n;
  __mark(0);

  while (__mark(1) & (i > 0)) {
    r = r + n;
    i--;
  }

  return r;
}
