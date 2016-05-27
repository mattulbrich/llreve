int foo(int heigh, int low) {
	for ( int i = 0; i < 6 ; i ++) {
		if ( i < 4)
			low = heigh ;
		else
			low = 3;
	}
	return low ;
}
