extern int __mark(int);
/*@ rel_in
(and
      (= votes$1 votes$2)
      (= res$1 res$2)
      (= length$1 length$2)
      (> length$1 2)
      (< (+ votes$1 length$1) res$1)
      (forall ((i Int))
              (and (= (select HEAP$1 i) (select HEAP$2 i))
                   (>= 1 (select HEAP$1 i))
                   (< (select HEAP$1 i) 10))))
  @*/
/*@ rel_out
  (forall ((i Int))
    (=> (and (>= i 0) (< i 10))
        (= (select HEAP$1 (+ result$1 i)) (select HEAP$2 (+ result$2 i)))))
  @*/
int anonymity(int *votes, int *res, int length) {
    int i = 0;

    int tmp = votes[1];
    votes[1] = votes[0];
    votes[0] = tmp;

    while (__mark(0) & (i < length)) {
        if (i < length) {
            res[votes[i]]++;
            i++;
        }
    }
    return res;
}
