int foo(int a, int b){
	a += b;
	b += 1;
	a -= b;
	a += 1;
	b += 1;
	return a;
}