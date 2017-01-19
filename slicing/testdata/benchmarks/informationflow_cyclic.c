#include "slicing_marks.h"

/* This is an interesting problem with a loop, which is not syntactically
 * sliceable. Each line is executable, but the assignment of c = 1 does
 * not influence the value of x: The assignment is only executed if c
 * already was below 3, in which case x is set to 3.
 *
 * Origin:
 * Martin Ward. “Properties of slicing definitions”. In: Source Code Analysis
 * and Manipulation, 2009. SCAM’09. Ninth IEEE International Working
 * Conference on. IEEE. 2009, pp. 23–32.
 */
int foo(int i, int c) {
	int x = 0;
	while (i < 5) {
		if (c < 3) {
			x = 3;
			__assert_sliced(
			c = 1);
		}
		i += 1;
	}
	return x;
}