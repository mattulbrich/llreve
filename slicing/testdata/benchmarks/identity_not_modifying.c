#include "slicing_marks.h"

// Simmelar to examples Listing 12
int foo ( int p ) {
	int x, y;
	__assert_sliced(
	y = p);
	x = p;
	if ( p ) {
		__assert_sliced(
		x = y);
	}
	return x ;
}