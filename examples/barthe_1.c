extern int __mark(int);

int f(int n, int c) {
    int i = 0;
    int j = 0;
    int x = 0;

    while (__mark(42) & (i < n)) {
        /* __mark(42); */
        j = 5 * i + c;
        x = x + j;
        i++;
    }
    return x;
}
