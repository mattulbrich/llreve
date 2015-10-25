extern int __mark(int);
int f(int x) {
    int i = 0;
    while (/*__mark(42) &*/ (i <= 10)) {
        __mark(42);
        if (i == x) {
            break;
        }
        i++;
    }
    return i;
}
