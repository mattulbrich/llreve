/*@ pre (and (>= a$1_0 0) (< b$1_0 n$1_0) (<= a$1_0 b$1_0)) @*/
int sep1(int *x, int n, int a, int b) {
    int cnt_even = 0;
    int cnt_odd = 0;
    for (int i = 0; i < n; i++) {
        int cur = (i == a ? x[b] : (i == b ? x[a] : x[i]));
        if (cur % 2 == 0)
            cnt_even++;
        else
            cnt_odd++;
    }
    return cnt_even - cnt_odd;
}
