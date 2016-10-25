extern int __mark(int);
double average(int n, int a[]) {
    if (n <= 0) {
        return 0;
    }
    int sum = 0;
    int i;

    for (i = 0; __mark(0) && (i < n); i++) {
        sum += a[i];
    }

    return (double)sum / n;
}
