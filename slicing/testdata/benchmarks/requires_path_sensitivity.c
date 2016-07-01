#include "slicing_marks.h"

// similar to example listing 11
// closer to the original example
int foo(int a, int z) {
	int x, y, b;
	x = 0;
	y = 5;

	if ( a > 0 )
		b = x + y;

	if ( a > 42)
		x = 1;
	else
		y = 0;

	if ( y > 0 ) {
		z = x;
		__criterion(z);
	}

	return z;
}
