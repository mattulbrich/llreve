#include "slicing_marks.h"

//NOTE: This is not represented in llvm. llvm will never include the line after the return value.

//Simelar to example listing 3
int foo ( int x ) {
	return x ;
	__assert_sliced(
	x += 5);
}