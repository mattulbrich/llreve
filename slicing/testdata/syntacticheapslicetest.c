#include "benchmarks/slicing_marks.h"

int foo(int* a, int x) {
	
	*a = 3;
	
	if(x == 5) {
		*a = 4;
	} else {
		*a = 2;
	}
	
	int b = *a;
	
	*a = 6; // sliced
	
	return b;
}
