extern int __mark(int);

int clearstr(int *a) {
   int i = 0;
   while(__mark(42) & (a[i] != 0)) {
      a[i] = 0;
      i++;
   }
   return i;
}
