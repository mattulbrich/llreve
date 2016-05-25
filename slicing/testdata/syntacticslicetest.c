int foo(int a) {
	int i;	// sliced
	i = 0;	// sliced
	i += 1;	// sliced
	if (a == 0) {	// sliced
		i += 2;	// sliced
	} else {
		i += 3;	// sliced
	}
	i += 4;	// sliced
	i += 5;	// sliced
	if (a == -1) {
		a -= -0;
	} else {
		a -= -2;
	}
	i += 6;	// sliced
	return a;
}