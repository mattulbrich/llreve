extern int __mark(int);

int findmax(int *a, int n) {

   int i = 1;
   int max = 0;
   int result;

   while(__mark(42) & (i < n)) {
      if(a[i] >= a[max]) {
         max = i;
      }
      i++;
   }

   result = a[max];
   return result;
}
