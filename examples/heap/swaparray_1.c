extern int __mark(int);
void swap(int *a, int *b, int n) {
    int i = 0;
    int t;
    while (__mark(42) & (i < n)) {
        t = a[i];
        a[i] = b[i];
        b[i] = t;
        i++;
    }
}
