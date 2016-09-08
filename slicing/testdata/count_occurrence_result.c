const int NO_ERROR = 0;
const int NULL_POINTER = -1;
const int OUT_OF_BOUND = -2;

int __criterion(int x){
	return x;
}

int countOccurrence(int x, int a[], int N) {
	int result = 0;
	int err = NO_ERROR;
	if (a == 0)
		err = NULL_POINTER;
	else
		for (int i = 0; i < N; i++) {
			if (0 <= i && i < N) {
				if (a[i] == x)
					result++;
			} else {
				err = OUT_OF_BOUND;
			}

			if (err)
				break;
		}

	__criterion(result);
	return err?err:result;
}
