#include "slicing_marks.h"

// Simmelar to examples Listing 12
int foo ( int p ) {
	int x, y;
	__assert_sliced(
	y = p + 0);
	x = p + 0;
	if ( p ) {
		__assert_sliced(
		x = y + 0);
	}
	return x ;
}