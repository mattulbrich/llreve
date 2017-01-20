#include "slicing_marks.h"

/*
 * Simple unreachable code. Note, that this is usually detected by the compiler.
 * The LLVM-IR does not contain the statement.
 */
int foo ( int x ) {
	return x ;
	__assert_sliced(
	x += 5);
}