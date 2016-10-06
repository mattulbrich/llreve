int f(int x, int *y) {
    int z = 42;
    if (x < 0) {
        y = &z;
    }
    return *y;
}
