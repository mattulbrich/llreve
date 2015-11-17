/*
Taken from:
  Relational verification using product programs
  Gilles Barthe, Juan Manuel Crespo, and Cesar Kunz
  IMDEA Software, Madrid, Spain
  FM 2011
  Page 4
*/
extern int __mark(int);
int f(int n) {
  int i = 0;
  int x = 0;
  while (__mark(1) & i <= n) {
    x = x + i;
    i++;
  }
  return x;
}
