int sep1(int *x, int n, int a, int b) {
    int cnt_even = 0;
    int cnt_odd = 0;
    for (int i = 0; i < n; i++) {
        int cur = x[i];
        if (cur % 2 == 0)
            cnt_even++;
        else
            cnt_odd++;
    }
    return cnt_even - cnt_odd;
}
