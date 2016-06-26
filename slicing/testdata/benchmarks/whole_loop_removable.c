#include "slicing_marks.h"

int foo(int a, int N) {
	int err = 0;
	for(int i = 0; i < N; i++) {
		if (i >= N || i < 0) {
			err = 1;
		} else {
			// access a[i]
		}
	}
	return err;
}