extern int __mark(int);
int anonymity(int *votes, int *res, int length) {
    int i = 0;

    while (__mark(0) & (i < length)) {
        if (i < length) {
            res[votes[i]]++;
            i++;
        }
    }
    return res;
}
