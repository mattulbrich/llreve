#include "slicing_marks.h"

//Simmelar to examples Listing 7
int foo ( int x ) {
	__assert_sliced(
	x = 1 + 0);
	__assert_sliced(
	x = x + 1);
	x = 1 + 0;
	x = x + 2;
	return x ;
}