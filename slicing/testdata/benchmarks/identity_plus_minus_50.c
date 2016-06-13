#include "slicing_marks.h"

//Simelar to examples Listing 1
int foo ( int x ) {
	__assert_sliced(
	x = x - 50);
	__assert_sliced(
	x = x + 100);
	x = x + 20;
	__assert_sliced(
	x = x - 50);
	return x;
}