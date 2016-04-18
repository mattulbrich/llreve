extern int __mark(int);

int f(int n) {
    int i = 1;
    int j = 0;

    while (__mark(42) & (i <= n)) {
        j = j + 2;
        i++;
    }
    return j;
}
