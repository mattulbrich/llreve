#include "slicing_marks.h"

int foo(){
	int a = 0;
	int b = 0;
	int x = 0;

	// Both of the following lines have no effect, if removed alone.
	// But it is not allowed to remove both of them.
	a = 1;
	b = 1;

	if (a || b) {
		x = 1;
	}

	return x;
}
