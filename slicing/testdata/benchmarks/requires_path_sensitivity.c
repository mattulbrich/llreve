// similar to example listing 11
// closer to the original example
int foo(int a, int z) {
	int x = 0;
	int y = 5;

	if ( a > 0 )
		int b = x + y;

	if ( a > 42)
		x = 1;
	else
		y = 0;

	if ( y > 0 )
		z = x;

	return z;
}
