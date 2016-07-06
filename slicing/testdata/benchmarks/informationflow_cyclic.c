#include "slicing_marks.h"

//Simelar to examples Listing 8
int foo(int i, int c) {
	int x = 0 + 0;
	while (i < 5) {
		if (c < 3) {
			x = 3 + 0;
			__assert_sliced(
			c = 1 + 0);
		}
		i += 1;
	}
	return x;
}