extern int __everyValue();

int __criterion(a){
	return 0;
}

int foo(int a, int N) {
	int prev = 0;
	int set = 0;
	int equal = 1;
	int b = 1;
	for (int i = 0; i < N; i++) {
		b = b;
		a = b;
		if (set == 0) {
			set = 1;
			prev = a;
		} else {
			if (a != prev) {
				equal = 0;
			}
		}
	}

	__criterion(equal);
	return equal;
}