extern int __mark(int);
float f(float n) {
    float i = 0;
    float j = 0;

    while (__mark(42) & (i <= n)) {
        i++;
        j++;
    }
    return j;
}
