extern int __mark(int);
float f(float n) {
    float i = n;
    float j = 0;

    while (__mark(42) & (i >= 0)) {
        i = i - 1;
        j++;
    }
    return j;
}
