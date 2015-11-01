extern int __mark(int);

int f(int n) {
    int r;
    int i;
    if (n <= 0) {
        r = n;
    } else {
        i = 0;
        while (__mark(42) & (i < n - 1)) {
            i = i + 1;
        }
        r = f(i);
    }
    return r;
}
