#include "slicing_marks.h"

const int NO_ERROR = 0;
const int NULL_POINTER = -1;
const int OUT_OF_BOUND = -2;

/*
 * This example is motivated by a simple method, that counts the occurrences
 * of a value in an array. The method contains error handling.
 * If we slice for result, everything with error can be removed. This is only
 * because the OUT_OF_BOUND error can not occur and therefore the break
 * will never happen.
 */
int countOccurrence(int x, int a[], int N) {
	int result = 0;
	int err = NO_ERROR;
	if (a == 0)
		err = NULL_POINTER;
	else
		for (int i = 0; i < N; i++) {
			if (0 <= i && i < N) {
				if (a[i] == x)
					result++;
			} else {
				err = OUT_OF_BOUND;
			}

			if (err)
				break;
		}

	__criterion(result);
	return err?err:result;
}
