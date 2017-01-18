#include "slicing_marks.h"

/**
 * This example shows that a fix point iteration may be useful for SLE and IAA.
 *
 * It is not possible to remove [1] or [3], unless [2] is removed first.
 */
int foo(){
	int k = 0;
	int x = 0;
	int a = 0;

	__assert_sliced(
	k = 5); // [1]
	__assert_sliced(
	a = 5); // [2]
	x = 5;

	if (a == 5) {
		__assert_sliced(
		x = 3);
		__assert_sliced(
		x = k); // [3]
	}

	return x;
}