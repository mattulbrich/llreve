int foo(int a) {
	int i;
	i = 0;
	i += 1;
	if (a == 0) {
		i += 2;
	} else {
		i+= 3;
	}
	i += 4;
	i += 5;
	if (a == -1) {
		a -= -1;
	} else {
		a -= -2;
	}
	i += 6;	
	return a + i;
}