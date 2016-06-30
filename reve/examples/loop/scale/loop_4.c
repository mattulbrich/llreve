extern int __mark(int);

int f(int n) {
    int x = 0;
    for (int i = 0; __mark(0) & (i < n); ++i) {
        ++x;
    }
    for (int i = 0; __mark(1) & (i < n); ++i) {
        ++x;
    }
    for (int i = 0; __mark(2) & (i < n); ++i) {
        ++x;
    }
    for (int i = 0; __mark(3) & (i < n); ++i) {
        ++x;
    }
    return x;
}
