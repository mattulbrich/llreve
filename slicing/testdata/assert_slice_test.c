int __criterion(int x){
	return x;
}

int __assert_sliced(int x){
	return x;
}

int foo(int x) {
	__assert_sliced(x += 0);
	__criterion(x);
	return x;
}