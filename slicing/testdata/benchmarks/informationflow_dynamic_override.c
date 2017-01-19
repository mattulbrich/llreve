	#include "slicing_marks.h"

/*
 * Assume, we are interested if the value of high can change the return value.
 * The interesting part is the assignment of z = y + 1: There is an input to
 * low where z is assigned to the return value, and there is also an input
 * to low where z will contains the high input. However, both can never
 * happen for the same value of low.
 */
int foo(int high, int low) {
	int low_result = 0;
	int y = 0;
	int z = 0;
	if ( low == 3) {
		__assert_sliced(
		y = high);
	}
	z = y + 1;
	if ( low != 3) {
		low_result = z ;
	}
	return low_result;
}
