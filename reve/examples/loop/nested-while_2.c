extern void __mark(int);

int f(int x, int g) {
    int i = 0;

    while (i < x) {
        __mark(23);
        i = i + 1;
        g = g - 1;
        while (x < i) {
            __mark(42);
            x = x + 1;
            g = g + 1;
        }
    }
    return g;
}
