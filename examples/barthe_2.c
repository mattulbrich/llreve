extern void __mark(int);

int f(int n, int c) {
    int i = 0;
    int j = c;
    int x = 0;

    while (i < n) {
        __mark(42);
        x = x + j;
        j = j + 5;
        i++;
    }
    return x;
}
