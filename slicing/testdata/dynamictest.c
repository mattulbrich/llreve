int foo(int a) {
	if(a == 1) {
		a = test(a);
	}
	return a + 1;
}

int test(int b) {
	return 2 * b;
}
