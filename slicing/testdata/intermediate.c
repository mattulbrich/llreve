void __criterion(int a){};

int foo(int a, int b, int c){
	int x = c;
	if ( a > 0) {
		x += 1;
		b += 1;
	}

	if ( x == c) {
		__criterion(b);
	}

	return b;
}

