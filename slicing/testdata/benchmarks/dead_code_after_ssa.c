#include "slicing_marks.h"

//Simmelar to examples Listing 7
int foo ( int x ) {
	__assert_sliced(x = 1);
	__assert_sliced(x = x);

	x = 1;
	x = x;
	return x ;
}