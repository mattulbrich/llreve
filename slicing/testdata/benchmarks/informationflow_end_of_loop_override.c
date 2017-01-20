#include "slicing_marks.h"

/*
 * Assume, we are interested if the value of high can change the return value.
 * Obviously, high is assigned to the return variable, therefore syntactic
 * will not solve this problem. The trick is, that the variable low is always
 * set to 3 in the last iteration of the loop. Therefore, the assignment of
 * high will be overwritten eventually.
 */
int foo(int high, int low, int N) {
	for ( int i = 0; i < N ; i ++) {
		if ( i < N - 1)
			__assert_sliced(
			low = high);
		else
			low = 3;
	}
	return low ;
}
