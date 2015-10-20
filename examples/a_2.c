extern void __mark(int);

int f(int n) {
   int i;
   int sum = 0;

   for(i = 0; i <= 10; i++) {
      __mark(0);
      if(i != 1)
         sum += i;
   }

   return i;
}
