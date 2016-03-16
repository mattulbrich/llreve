extern int __mark(int);
int mono(int *res, int C) {
    int max = 0;
    int elect = 0;

    for (int i = 1; __mark(0) & (i <= C); ++i) {
        if (max < res[i]) {
            max = res[i];
            elect = i;
        } else if (max == res[i]) {
            elect = 0;
        }
    }
    return elect;
}
