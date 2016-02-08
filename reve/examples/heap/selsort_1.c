extern int __mark(int);

void selsort(int *a, int n) {

   int i;
   int j;
   int t;

   i = 0;
   while(__mark(1) & (i < n)) {
      j = i;
      while(__mark(2) & (j < n)) {
         if(a[j] <= a[i]) {
            t = a[i];
            a[i] = a[j];
            a[j] = t;
         }
         j++;
      }
      i++;
   }
}
