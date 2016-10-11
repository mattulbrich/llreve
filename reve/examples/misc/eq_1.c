int g(int x) {
    return x;
}
// extern int g(int x);
extern int h(int x);
int f(int x) {
    x = g(x);
    x = h(x);
    return x;
}
