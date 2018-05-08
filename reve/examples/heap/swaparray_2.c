/*@ rel_in (and (= a$1 a$2) (= b$1 b$2) (= n$1 n$2) (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i))) (> a$1 (+ b$1 n$1))) @*/
extern int __mark(int);

void swap(int *a, int *b, int n) {
   int *start = a;
   while(__mark(42) & (a-start < n)) {
      *a = *a+*b;
      *b = *a-*b;
      *a = *a-*b;
      a++;
      b++;
   }
}
