/*@ rel_in (and (= a$1_0 a$2_0) (= b$1_0 b$2_0) (= n$1_0 n$2_0) (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i))) (> a$1_0 (+ b$1_0 n$1_0))) @*/
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
