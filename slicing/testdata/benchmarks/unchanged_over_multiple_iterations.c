#include "slicing_marks.h"

/*
 * The value of x is alternating incremented and decremented.
 * As the number of iterations is even, the final value of x
 * is not changed and the loop is unnecessary.
 *
 * Author: Demian Hespe.
 */
int foo (int x, int N) {
  for (int i = 0; i < 2 * N; i++) {
    int a = -1;
    if (i % 2 == 0) {
      __assert_sliced(
      a = 1);
    }
    x += a;
  }

  return x;
}