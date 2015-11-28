extern int __mark(int);

int equalize(int *a, int n) {

   int i = 0;

   while(__mark(42) & (i < n)) {
      a[i+1] = a[i];
      i++;
   }

   return i;
}
