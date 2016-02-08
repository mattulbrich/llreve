extern int __mark(int);

int findmax(int *a, int n) {

   int i = 1;
   int maxv = a[0];
   int result;

   while(__mark(42) & (i < n)) {
      if(a[i] >= maxv) {
         maxv = a[i];
      }
      i++;
   }

   result = maxv;
   return result;
}
