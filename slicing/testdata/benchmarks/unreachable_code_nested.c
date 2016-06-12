// Simmelar to Listing 4, precondition replaced by additional if
int foo ( int x ) {
	if (x > 0) {
		if ( x < 0) {
			x = -x ;
		}
	}
	return x ;
}