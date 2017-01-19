#include "slicing_marks.h"

/* A very simple example, that is also sliceable syntactically.
 * The variable y is set but never used.
 */
int foo ( int x ) {
	int y;
	x = x + 3;
	__assert_sliced(
	y = 5);
	return x;
}