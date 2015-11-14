extern int __mark(int);

int f(int n) {
    int i = 1;
    int j = 2;

    if (n < 1) {
        n = 1;
    }

    __mark(23);
    while (__mark(42) & i < n) {
        j = j + 2;
        i++;
    }

    return j;
}
