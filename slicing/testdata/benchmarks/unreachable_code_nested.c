#include "slicing_marks.h"

// Simmelar to Listing 4, precondition replaced by additional if
int foo ( int x ) {
	if (x > 0) {
		if ( x < 0) {
			__assert_sliced(
			x += 42);
		}
	}
	return x ;
}