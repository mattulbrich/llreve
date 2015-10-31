extern void __mark(int);

int f(int n) {
    int i = 1;
    int j = 0;

    while (i <= n) {
        __mark(42);
        j = j + 2;
        i++;
    }
    return j;
}
