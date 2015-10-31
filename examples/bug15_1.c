extern void __mark(int);

int f(int z) {
    int x = 1;
    int y = 0;

    while (x <= 9) {
        __mark(42);
        y = x + 2;
        x = 2 * y;
    }

    return 2 * x;
}
