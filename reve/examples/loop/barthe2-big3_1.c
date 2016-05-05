/*@ opt -nest @*/
extern int __mark(int);
int f(int n) {
    int i = 1;
    int x = 1;

    while (__mark(1) & (i <= n)) {
        x = x * 1;
        i++;
    }

    i = 0;
    while (__mark(2) & (i <= n)) {
        x = x + i;
        i++;
    }

    i = 1;
    while (__mark(3) & (i <= n)) {
        x = x * 2;
        i++;
    }

    int k = n;
    while (__mark(4) & (n >= 0)) {
        x = x + n;
        n--;
    }

    return x;
}
