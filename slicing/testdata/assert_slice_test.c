int __criterion(int x){
	return x;
}

int __assert_sliced(int x){
	return x;
}

int foo(int x) {

	x += 0;
	x += 0;

	__criterion(x);
	return x;
}