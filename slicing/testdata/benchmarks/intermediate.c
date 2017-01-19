#include "slicing_marks.h"

/*
 * A simple example for an intermediate slicing criterion.
 * If the criterion is executed, then the increment of b was not
 * executed and therefore does not participate to the value of b
 * at the criterion. Note, that the increment of x does influence
 * weather the criterion is executed, and therefore can not be sliced.
 */
int foo(int a, int b, int c){
	int x = c;
	if ( a > 0) {
		x += 1;
		b += 1;
	}

	if ( x == c) {
		__criterion(b);
	}

	return b;
}

