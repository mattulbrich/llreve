extern int __mark(int);
/*@ pre (bvsle n$1_0__1 (_ bv10000000 32)) @*/

int f(int n) {
    int i = 1;
    int j = 0;

    while (__mark(42) & (i <= n)) {
        j = j + 2;
        i++;
    }
    return j;
}
