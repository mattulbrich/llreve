#include "benchmarks/slicing_marks.h"

int foo(int x) {
	__assert_sliced(x += 0);
	return x;
}