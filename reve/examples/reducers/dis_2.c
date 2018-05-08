/*@ pre (and (>= a$1 0) (< b$1 n$1) (< a$1 b$1)) @*/
int dis(int *x, int n, int a, int b) {
    int res = 0;
    int cnt = 0;
    for (int i = 0; i < n; i++) {
        int cur = (i == a ? x[b] : (i == b ? x[a] : x[i]));
        if (cur > 10000) {
            res += cur;
            cnt += 1;
        }
    }
    return res / cnt;
}
