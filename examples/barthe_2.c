extern int __mark(int);

int f(int n, int c) {
    int i = 0;
    int j = c;
    int x = 0;

    while (__mark(42) & (i < n)) {
        /* __mark(42); */
        x = x + j;
        j = j + 5;
        i++;
    }
    return x;
}
