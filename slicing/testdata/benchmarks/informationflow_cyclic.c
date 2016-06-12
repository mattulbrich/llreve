//Simelar to examples Listing 8
int foo(int i, int c) {
	int x = 0
	while (i < 5) {
		if (c < 3) {
			x = 3;
			c = 1;
		}
		i += 1;
	}
	return x;
}