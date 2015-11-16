extern int __mark(int);
int f(int m) {
    int result;

    if (m > 0) {
        result = tr(m - 1);
        if (result >= 0) {
            result = result + m;
        }
    } else {
        result = 0;
    }

    return result;
}

int tr(int n) {
    int result;
    int i;

    i = 0;
    result = 0;
    while (__mark(42) & (i < n)) {
        result = result + i;
    }

    return result;
}
