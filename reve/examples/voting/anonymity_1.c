extern int __mark(int);
void anonymity(int *votes, int *res, int length, int v, int w) {
    int i = 0;

    while (__mark(0) & (i < length)) {
        if (i < length) {
            res[votes[i]]++;
            i++;
        }
    }
}
