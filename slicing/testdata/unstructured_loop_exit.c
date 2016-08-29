int foo(int N) {
	int x = 0;
	while (1) {
		for (int i = 0; i < N; i++) {
			if (i == 3) {
				return 42;
			}
		}
	}

	return x;
}