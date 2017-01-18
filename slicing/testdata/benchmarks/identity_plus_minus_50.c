#include "slicing_marks.h"

/* The Idea of this program is that consecutive arithmetic operations are
 * canceled out by each other. The statements can only be removed together.
 * Therefore, only the BF method can solve this problem.
 * In contrast to the original version, the sliceable statements
 * are discontiguous.
 *
 * Origin:
 * José Bernardo Barros et al. “Assertion-based slicing and slice graphs”. In:
 * Formal Aspects of Computing 24.2 (2012), pp. 217–248.
 */
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