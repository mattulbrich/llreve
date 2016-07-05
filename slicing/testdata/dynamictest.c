
int loop(int N) {
	N = 2;
	int x = 0;
	int i = 0;
	while(i < N) {
		if(i == 0) {
			x = 5;
		} else {
			x = i;
		}
		i++;
	}
	return x;
}

/*
int foo(int a) {
	if(a == 0) {
		a = test(a);
	}
	return a + 1;
}

int test(int b) {
	return 2 * b;
}
*/