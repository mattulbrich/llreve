#include "slicing_marks.h"

int foo(){
	int k = 0;
	int x = 0;
	int a = 0;

	__assert_sliced(
	k = 5
	);
	__assert_sliced(
	a = 5
	);
	x = 5;

	if (a == 5) {
		__assert_sliced(
		x = 3
		);
		__assert_sliced(
		x = k
		);
	}

	return x;
}

/**
 * It is not possible to remove line 9 or 21, unless line 13 is removed first. 
 * Simple ordering of the statements to be checked dose not allow each line to
 * be checked only once.
 * 
 * Orders that do not work are:
 * 	* first statement first
 * 	* last statement first
 * 	* PDG as DAG, check statements with no predecessor first than remove.
 *
 * What may work:
 * 	* Priority queue, insert statements from PDG predecessor. Follow control flow edges first.
 */