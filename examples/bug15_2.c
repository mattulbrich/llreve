extern void __mark(int);

int f(int z) {
    int y = 0;
    int x = 1;

    while (x < 10) {
        __mark(42);
        y = 2 + x;
        x = y + y;
    }

    return x * 2;
}
