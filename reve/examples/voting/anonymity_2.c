extern int __mark(int);
/*@ rel_in
(and
      (= votes$1_0 votes$2_0)
      (= res$1_0 res$2_0)
      (= length$1_0 length$2_0)
      (= v$1_0 v$2_0)
      (= w$1_0 w$2_0)
      (>= length$1_0 0)
      (< v$1_0 length$1_0)
      (>= v$1_0 0)
      (>= w$1_0 0)
      (< w$1_0 length$1_0)
      (< (+ votes$1_0 length$1_0) res$1_0)
      (forall ((i Int))
              (and (= (select HEAP$1 i) (select HEAP$2 i))
                   (>= 1 (select HEAP$1 i))
                   (< (select HEAP$1 i) 10))))
@*/
void anonymity(int *votes, int *res, int length, int v, int w) {
    int i = 0;

    int tmp = votes[v];
    votes[v] = votes[w];
    votes[w] = tmp;

    while (__mark(0) & (i < length)) {
        if (i < length) {
            res[votes[i]]++;
            i++;
        }
    }
    votes[w] = votes[v];
    votes[v] = tmp;
}
