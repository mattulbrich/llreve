extern int __mark(int);

int clearstr(int *a) {
   int *a0 = a;
   while(__mark(42) & (*a != 0)) {
      *a = 0;
      a++;
   }
   return a-a0;
}
