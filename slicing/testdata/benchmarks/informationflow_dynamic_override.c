#include "slicing_marks.h"

//Simelar to examples Listing 9
int foo(int heigh, int low_x) {
	int low_result = 0;
	int y = 0;
	int z = 0;
	if ( low_x == 3) {
		__assert_sliced(
		y = heigh);
	}
	z = y + 1;
	if ( low_x != 3) {
		low_result = z ;
	}
	return low_result;
}
