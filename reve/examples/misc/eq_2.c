int a(int x) {
    return x;
}
// extern int a(int x);
extern int b(int x);
int f(int x) {
    x = a(x);
    x = b(x);
    return x;
}
