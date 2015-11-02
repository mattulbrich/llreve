extern int __mark(int);
int f(int m, int n) {
    int r;
    int x;
    x = 0;
    r = 0;
    if (m > 0 && n == 0) {
        __mark(23);
        r = f(m - 1, 1);
    } else {
        if (m == 0) {
            r = n + 1;
        } else {
            __mark(42);
            x = f(m, n - 1);
            r = f(m - 1, x);
        }
    }
    return r;
}
