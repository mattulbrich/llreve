extern int __mark(int);
int f(int x) {
    int i = 10;
    while (__mark(42) & (i >= 0)) {
        if (i == (10 - x)) {
            break;
        }
        i--;
    }
    return 10 - i;
}
