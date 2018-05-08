/*@ pre (> C$1 1) @*/
/*@ rel_out (=> (= result$1 1) (= result$2 1)) @*/
extern int __mark(int);
int mono(int *res, int C) {
    int max = 0;
    int elect = 0;

    res[1]++;

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
