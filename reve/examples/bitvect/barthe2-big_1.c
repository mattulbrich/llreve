/*@ pre (bvsge n$1_0__1 (_ bv0 32)) (bvsle n$1_0__1 (_ bv13 32)) @*/
extern int __mark(int);
int f(int n) {
    int i = 1;
    int x = 1;

    while (__mark(1) & i <= n) {
        x = x * 5;
        i++;
    }

    i = 0;

    while (__mark(2) & i <= n) {
        x = x + i;
        i++;
    }
    return x;
}
