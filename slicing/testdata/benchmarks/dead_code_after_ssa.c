#include "slicing_marks.h"

//Simmelar to examples Listing 7
int foo ( int x ) {
	__assert_sliced(x = 2);
	__assert_sliced(x = x);

	x = 1;
	return x ;
}