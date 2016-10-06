int avg1(int *x, int n, int a, int b) {
    int res = 0;
    int cnt = 0;
    int i = 0;
    for (int i = 0; i < n; i++) {
        res += x[i];
        cnt += 1;
    }
    return res / cnt;
}
