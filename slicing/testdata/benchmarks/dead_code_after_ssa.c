#include "slicing_marks.h"

/* A very simple example, that is also sliceable syntactically.
 * The variable x is set multiple times, without being used in between.
 */
int foo ( int x ) {
	__assert_sliced(x = 2);
	__assert_sliced(x = x);

	x = 1;
	return x ;
}