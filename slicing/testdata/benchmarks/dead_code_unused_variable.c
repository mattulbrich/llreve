#include "slicing_marks.h"

//Simmelar to examples Listing 2
int foo ( int x ) {
	int y;
	x = x + 3;
	__assert_sliced(
	y = 5);
	return x;
}