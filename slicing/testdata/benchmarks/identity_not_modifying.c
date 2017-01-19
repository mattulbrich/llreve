#include "slicing_marks.h"

/* In this example two variables do have the same value and the additional
 * assignment can be removed. The branch is necessary, because if x is always
 * set to y, the previous assignment to p would be unnecessary and the problem
 * could be solved syntactically.
 *
 * Origin:
 * John Field, Ganesan Ramalingam, and Frank Tip. “Parametric program
 * slicing”. In: Proceedings of the 22nd ACM SIGPLAN-SIGACT symposium
 * on Principles of programming languages. ACM. 1995, pp. 379–392.
 */
int foo ( int p ) {
	int x, y;
	__assert_sliced(
	y = p);
	x = p;
	if ( p ) {
		__assert_sliced(
		x = y);
	}
	return x ;
}