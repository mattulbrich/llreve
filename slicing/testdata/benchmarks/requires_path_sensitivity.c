#include "slicing_marks.h"

/*
 * The first assignment of x can be removed as the assignment z = x
 * is only executed if the assignment x = 1 happens. This is not
 * detectable by syntactic slicing.
 * The assignment to b can be removed syntactically.
 * In [1] Fig 1 it is also stated that y = 0 could be removed,
 * however, we have a different opinion (and our tool as well).
 *
 * Origin:
 * [1] Joxan Jaffar et al. “Path-sensitive backward slicing”. In: Static Analysis.
 * Springer, 2012, pp. 231–247.
 */
int foo(int a, int z, int x, int y, int b) {
	__assert_sliced(
	x = 0);
	y = 5;

	if ( a > 0 )
		b = x + y;

	if ( a > 42)
		x = 1;
	else
		y = 0;

	if ( y > 0 ) {
		z = x;
	}

	return z;
}
