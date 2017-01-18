#include "slicing_marks.h"

/*
 * The assignment can be removed, but not syntactically. Our algorithm
 * is not able to remove the whole loop, as the slice is required to have
 * the same number of iterations as the original program for each loop.
 * However, after our tool removed the assignment to err, a syntactic slice
 * can be used for post processing and clean up and remove the loop.
 */
int foo(int a, int N) {
	int err = 0;
	for(int i = 0; i < N; i++) {
		if (i >= N || i < 0) {
			__assert_sliced(
			err = 1);
		} else {
			// access a[i]
		}
	}
	return err;
}