/*
 * These two programs differ in the number of iterations of the
 * loop. This versions does one more iteration with n = 0, while
 * the other version adds one to the output value.
 *
 * Do they compute the same?
 * No, not in general.
 * But they do for non-negative integers. That's why there is
 * the precondition in the second release. Drop it and you'll
 * get a counterexample (n=-1, e.g.)
 */
/*
 * These two programs differ in the number of iterations of the
 * loop. This versions does one more iteration with n = 0, while
 * the other version adds one to the output value.
 *
 * Do they compute the same?
 * No, not in general.
 * But they do for non-negative integers. That's why there is
 * the precondition in the second release. Drop it and you'll
 * get a counterexample (n=-1, e.g.)
 */
extern int __mark(int);
int upcount(int n) {

   int m = 0;
   while(__mark(42) & (n >= 0)) {
      m++;
      n--;
   }
   return m;
}
