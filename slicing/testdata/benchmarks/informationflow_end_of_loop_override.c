#include "slicing_marks.h"

//Simelar to examples Listing 10
int foo(int heigh, int low, int N) {
	for ( int i = 0; i < N ; i ++) {
		if ( i < N - 1)
			__assert_sliced(
			low = heigh);
		else
			low = 3;
	}
	return low ;
}
