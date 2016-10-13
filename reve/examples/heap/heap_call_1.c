/*@ opt -fun f @*/
int g(int *b);
int f(int a, int* b) {
  a = g(b);
  a = *b;
  return a;
}

int g(int *b) {
  *b = 1;
  return 0;
}
