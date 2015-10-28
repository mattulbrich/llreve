extern int __mark(int);
int f(int x) {
    int i = 0;
    while (__mark(42) & ((i <= 10) && (i != x))) {
        /* __mark(42); */
        i++;
    }
    return i;
}
