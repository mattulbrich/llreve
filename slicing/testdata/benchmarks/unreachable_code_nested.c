#include "slicing_marks.h"

/*
 * The line is sliceable, because it is never executed anyway.
 */
int foo ( int x ) {
	if (x > 0) {
		if ( x < 0) {
			__assert_sliced(
			x += 42);
		}
	}
	return x ;
}