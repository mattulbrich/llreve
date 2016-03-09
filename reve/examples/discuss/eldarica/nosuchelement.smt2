(set-logic HORN)
(define-fun
   IN_INV
   ((votes$1_0 Int)
    (res$1_0 Int)
    (length$1_0 Int)
    (v$1_0 Int)
    (w$1_0 Int)
    (HEAP$1 (Array Int Int))
    (votes$2_0 Int)
    (res$2_0 Int)
    (length$2_0 Int)
    (v$2_0 Int)
    (w$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
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
                   (< (select HEAP$1 i) 10)))))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
(declare-fun
   INV_MAIN_0
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((votes$1_0_old Int)
       (res$1_0_old Int)
       (length$1_0_old Int)
       (v$1_0_old Int)
       (w$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (votes$2_0_old Int)
       (res$2_0_old Int)
       (length$2_0_old Int)
       (v$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV votes$1_0_old res$1_0_old length$1_0_old v$1_0_old w$1_0_old HEAP$1_old votes$2_0_old res$2_0_old length$2_0_old v$2_0_old w$2_0_old HEAP$2_old)
         (let
            ((votes$1_0 votes$1_0_old)
             (res$1_0 res$1_0_old)
             (length$1_0 length$1_0_old)
             (v$1_0 v$1_0_old)
             (w$1_0 w$1_0_old)
             (HEAP$1 HEAP$1_old)
             (i.0$1_0 0)
             (votes$2_0 votes$2_0_old)
             (res$2_0 res$2_0_old)
             (length$2_0 length$2_0_old)
             (v$2_0 v$2_0_old))
            (let
               ((w$2_0 w$2_0_old)
                (HEAP$2 HEAP$2_old)
                (_$2_0 v$2_0))
               (let
                  ((_$2_1 (+ votes$2_0 (* 4 _$2_0))))
                  (let
                     ((_$2_2 (select HEAP$2 _$2_1))
                      (_$2_3 w$2_0))
                     (let
                        ((_$2_4 (+ votes$2_0 (* 4 _$2_3))))
                        (let
                           ((_$2_5 (select HEAP$2 _$2_4))
                            (_$2_6 v$2_0))
                           (let
                              ((_$2_7 (+ votes$2_0 (* 4 _$2_6))))
                              (let
                                 ((HEAP$2 (store HEAP$2 _$2_7 _$2_5))
                                  (_$2_8 w$2_0))
                                 (let
                                    ((_$2_9 (+ votes$2_0 (* 4 _$2_8))))
                                    (let
                                       ((HEAP$2 (store HEAP$2 _$2_9 _$2_2))
                                        (i.0$2_0 0))
                                       (forall
                                          ((i1 Int)
                                           (i2 Int))
                                          (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (length$1_0_old Int)
       (res$1_0_old Int)
       (votes$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_2_old Int)
       (i.0$2_0_old Int)
       (length$2_0_old Int)
       (res$2_0_old Int)
       (v$2_0_old Int)
       (votes$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((res$1_0 res$1_0_old)
                (votes$1_0 votes$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (< i.0$1_0 length$1_0)))
               (=>
                  (not _$1_1)
                  (let
                     ((result$1 0)
                      (HEAP$1_res HEAP$1)
                      (_$2_2 _$2_2_old)
                      (i.0$2_0 i.0$2_0_old)
                      (length$2_0 length$2_0_old))
                     (let
                        ((res$2_0 res$2_0_old)
                         (v$2_0 v$2_0_old)
                         (votes$2_0 votes$2_0_old)
                         (w$2_0 w$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (_$2_11 (< i.0$2_0 length$2_0)))
                        (=>
                           (not _$2_11)
                           (let
                              ((_$2_21 v$2_0))
                              (let
                                 ((_$2_22 (+ votes$2_0 (* 4 _$2_21))))
                                 (let
                                    ((_$2_23 (select HEAP$2 _$2_22))
                                     (_$2_24 w$2_0))
                                    (let
                                       ((_$2_25 (+ votes$2_0 (* 4 _$2_24))))
                                       (let
                                          ((HEAP$2 (store HEAP$2 _$2_25 _$2_23))
                                           (_$2_26 v$2_0))
                                          (let
                                             ((_$2_27 (+ votes$2_0 (* 4 _$2_26))))
                                             (let
                                                ((HEAP$2 (store HEAP$2 _$2_27 _$2_2)))
                                                (let
                                                   ((result$2 0)
                                                    (HEAP$2_res HEAP$2))
                                                   (OUT_INV result$1 result$2 HEAP$1_res HEAP$2_res))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (length$1_0_old Int)
       (res$1_0_old Int)
       (votes$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_2_old Int)
       (i.0$2_0_old Int)
       (length$2_0_old Int)
       (res$2_0_old Int)
       (v$2_0_old Int)
       (votes$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((res$1_0 res$1_0_old)
                (votes$1_0 votes$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (< i.0$1_0 length$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 (< i.0$1_0 length$1_0)))
                     (=>
                        _$1_2
                        (let
                           ((_$1_3 i.0$1_0))
                           (let
                              ((_$1_4 (+ votes$1_0 (* 4 _$1_3))))
                              (let
                                 ((_$1_5 (select HEAP$1 _$1_4)))
                                 (let
                                    ((_$1_6 _$1_5))
                                    (let
                                       ((_$1_7 (+ res$1_0 (* 4 _$1_6))))
                                       (let
                                          ((_$1_8 (select HEAP$1 _$1_7)))
                                          (let
                                             ((_$1_9 (+ _$1_8 1)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 _$1_7 _$1_9))
                                                 (_$1_10 (+ i.0$1_0 1)))
                                                (let
                                                   ((i.0$1_0 _$1_10)
                                                    (_$2_2 _$2_2_old)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (length$2_0 length$2_0_old))
                                                   (let
                                                      ((res$2_0 res$2_0_old)
                                                       (v$2_0 v$2_0_old)
                                                       (votes$2_0 votes$2_0_old)
                                                       (w$2_0 w$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (_$2_11 (< i.0$2_0 length$2_0)))
                                                      (=>
                                                         _$2_11
                                                         (let
                                                            ((_$2_12 (< i.0$2_0 length$2_0)))
                                                            (=>
                                                               _$2_12
                                                               (let
                                                                  ((_$2_13 i.0$2_0))
                                                                  (let
                                                                     ((_$2_14 (+ votes$2_0 (* 4 _$2_13))))
                                                                     (let
                                                                        ((_$2_15 (select HEAP$2 _$2_14)))
                                                                        (let
                                                                           ((_$2_16 _$2_15))
                                                                           (let
                                                                              ((_$2_17 (+ res$2_0 (* 4 _$2_16))))
                                                                              (let
                                                                                 ((_$2_18 (select HEAP$2 _$2_17)))
                                                                                 (let
                                                                                    ((_$2_19 (+ _$2_18 1)))
                                                                                    (let
                                                                                       ((HEAP$2 (store HEAP$2 _$2_17 _$2_19))
                                                                                        (_$2_20 (+ i.0$2_0 1)))
                                                                                       (let
                                                                                          ((i.0$2_0 _$2_20))
                                                                                          (forall
                                                                                             ((i1 Int)
                                                                                              (i2 Int))
                                                                                             (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (length$1_0_old Int)
       (res$1_0_old Int)
       (votes$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_2_old Int)
       (i.0$2_0_old Int)
       (length$2_0_old Int)
       (res$2_0_old Int)
       (v$2_0_old Int)
       (votes$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((res$1_0 res$1_0_old)
                (votes$1_0 votes$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (< i.0$1_0 length$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 (< i.0$1_0 length$1_0)))
                     (=>
                        _$1_2
                        (let
                           ((_$1_3 i.0$1_0))
                           (let
                              ((_$1_4 (+ votes$1_0 (* 4 _$1_3))))
                              (let
                                 ((_$1_5 (select HEAP$1 _$1_4)))
                                 (let
                                    ((_$1_6 _$1_5))
                                    (let
                                       ((_$1_7 (+ res$1_0 (* 4 _$1_6))))
                                       (let
                                          ((_$1_8 (select HEAP$1 _$1_7)))
                                          (let
                                             ((_$1_9 (+ _$1_8 1)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 _$1_7 _$1_9))
                                                 (_$1_10 (+ i.0$1_0 1)))
                                                (let
                                                   ((i.0$1_0 _$1_10)
                                                    (_$2_2 _$2_2_old)
                                                    (i.0$2_0 i.0$2_0_old)
                                                    (length$2_0 length$2_0_old))
                                                   (let
                                                      ((res$2_0 res$2_0_old)
                                                       (v$2_0 v$2_0_old)
                                                       (votes$2_0 votes$2_0_old)
                                                       (w$2_0 w$2_0_old)
                                                       (HEAP$2 HEAP$2_old)
                                                       (_$2_11 (< i.0$2_0 length$2_0)))
                                                      (=>
                                                         _$2_11
                                                         (let
                                                            ((_$2_12 (< i.0$2_0 length$2_0)))
                                                            (=>
                                                               (not _$2_12)
                                                               (let
                                                                  ((i.0$2_0 i.0$2_0))
                                                                  (forall
                                                                     ((i1 Int)
                                                                      (i2 Int))
                                                                     (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (length$1_0_old Int)
       (res$1_0_old Int)
       (votes$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_2_old Int)
       (i.0$2_0_old Int)
       (length$2_0_old Int)
       (res$2_0_old Int)
       (v$2_0_old Int)
       (votes$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((res$1_0 res$1_0_old)
                (votes$1_0 votes$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (< i.0$1_0 length$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 (< i.0$1_0 length$1_0)))
                     (=>
                        (not _$1_2)
                        (let
                           ((i.0$1_0 i.0$1_0)
                            (_$2_2 _$2_2_old)
                            (i.0$2_0 i.0$2_0_old)
                            (length$2_0 length$2_0_old))
                           (let
                              ((res$2_0 res$2_0_old)
                               (v$2_0 v$2_0_old)
                               (votes$2_0 votes$2_0_old)
                               (w$2_0 w$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (_$2_11 (< i.0$2_0 length$2_0)))
                              (=>
                                 _$2_11
                                 (let
                                    ((_$2_12 (< i.0$2_0 length$2_0)))
                                    (=>
                                       _$2_12
                                       (let
                                          ((_$2_13 i.0$2_0))
                                          (let
                                             ((_$2_14 (+ votes$2_0 (* 4 _$2_13))))
                                             (let
                                                ((_$2_15 (select HEAP$2 _$2_14)))
                                                (let
                                                   ((_$2_16 _$2_15))
                                                   (let
                                                      ((_$2_17 (+ res$2_0 (* 4 _$2_16))))
                                                      (let
                                                         ((_$2_18 (select HEAP$2 _$2_17)))
                                                         (let
                                                            ((_$2_19 (+ _$2_18 1)))
                                                            (let
                                                               ((HEAP$2 (store HEAP$2 _$2_17 _$2_19))
                                                                (_$2_20 (+ i.0$2_0 1)))
                                                               (let
                                                                  ((i.0$2_0 _$2_20))
                                                                  (forall
                                                                     ((i1 Int)
                                                                      (i2 Int))
                                                                     (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (length$1_0_old Int)
       (res$1_0_old Int)
       (votes$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_2_old Int)
       (i.0$2_0_old Int)
       (length$2_0_old Int)
       (res$2_0_old Int)
       (v$2_0_old Int)
       (votes$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((res$1_0 res$1_0_old)
                (votes$1_0 votes$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (< i.0$1_0 length$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 (< i.0$1_0 length$1_0)))
                     (=>
                        (not _$1_2)
                        (let
                           ((i.0$1_0 i.0$1_0)
                            (_$2_2 _$2_2_old)
                            (i.0$2_0 i.0$2_0_old)
                            (length$2_0 length$2_0_old))
                           (let
                              ((res$2_0 res$2_0_old)
                               (v$2_0 v$2_0_old)
                               (votes$2_0 votes$2_0_old)
                               (w$2_0 w$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (_$2_11 (< i.0$2_0 length$2_0)))
                              (=>
                                 _$2_11
                                 (let
                                    ((_$2_12 (< i.0$2_0 length$2_0)))
                                    (=>
                                       (not _$2_12)
                                       (let
                                          ((i.0$2_0 i.0$2_0))
                                          (forall
                                             ((i1 Int)
                                              (i2 Int))
                                             (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2)))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (length$1_0_old Int)
       (res$1_0_old Int)
       (votes$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_2_old Int)
       (i.0$2_0_old Int)
       (length$2_0_old Int)
       (res$2_0_old Int)
       (v$2_0_old Int)
       (votes$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((res$1_0 res$1_0_old)
                (votes$1_0 votes$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (< i.0$1_0 length$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 (< i.0$1_0 length$1_0)))
                     (=>
                        _$1_2
                        (let
                           ((_$1_3 i.0$1_0))
                           (let
                              ((_$1_4 (+ votes$1_0 (* 4 _$1_3))))
                              (let
                                 ((_$1_5 (select HEAP$1 _$1_4)))
                                 (let
                                    ((_$1_6 _$1_5))
                                    (let
                                       ((_$1_7 (+ res$1_0 (* 4 _$1_6))))
                                       (let
                                          ((_$1_8 (select HEAP$1 _$1_7)))
                                          (let
                                             ((_$1_9 (+ _$1_8 1)))
                                             (let
                                                ((HEAP$1 (store HEAP$1 _$1_7 _$1_9))
                                                 (_$1_10 (+ i.0$1_0 1)))
                                                (let
                                                   ((i.0$1_0 _$1_10))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((_$2_2 _$2_2_old)
                                                             (i.0$2_0 i.0$2_0_old)
                                                             (length$2_0 length$2_0_old))
                                                            (let
                                                               ((res$2_0 res$2_0_old)
                                                                (v$2_0 v$2_0_old)
                                                                (votes$2_0 votes$2_0_old)
                                                                (w$2_0 w$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (_$2_11 (< i.0$2_0 length$2_0)))
                                                               (=>
                                                                  _$2_11
                                                                  (let
                                                                     ((_$2_12 (< i.0$2_0 length$2_0)))
                                                                     (=>
                                                                        _$2_12
                                                                        (let
                                                                           ((_$2_13 i.0$2_0))
                                                                           (let
                                                                              ((_$2_14 (+ votes$2_0 (* 4 _$2_13))))
                                                                              (let
                                                                                 ((_$2_15 (select HEAP$2 _$2_14)))
                                                                                 (let
                                                                                    ((_$2_16 _$2_15))
                                                                                    (let
                                                                                       ((_$2_17 (+ res$2_0 (* 4 _$2_16))))
                                                                                       (let
                                                                                          ((_$2_18 (select HEAP$2 _$2_17)))
                                                                                          (let
                                                                                             ((_$2_19 (+ _$2_18 1)))
                                                                                             (let
                                                                                                ((HEAP$2 (store HEAP$2 _$2_17 _$2_19))
                                                                                                 (_$2_20 (+ i.0$2_0 1)))
                                                                                                (let
                                                                                                   ((i.0$2_0 _$2_20))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((_$2_2 _$2_2_old)
                                                             (i.0$2_0 i.0$2_0_old)
                                                             (length$2_0 length$2_0_old))
                                                            (let
                                                               ((res$2_0 res$2_0_old)
                                                                (v$2_0 v$2_0_old)
                                                                (votes$2_0 votes$2_0_old)
                                                                (w$2_0 w$2_0_old)
                                                                (HEAP$2 HEAP$2_old)
                                                                (_$2_11 (< i.0$2_0 length$2_0)))
                                                               (=>
                                                                  _$2_11
                                                                  (let
                                                                     ((_$2_12 (< i.0$2_0 length$2_0)))
                                                                     (=>
                                                                        (not _$2_12)
                                                                        (let
                                                                           ((i.0$2_0 i.0$2_0))
                                                                           false)))))))
                                                      (forall
                                                         ((i1 Int)
                                                          (i2_old Int))
                                                         (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (length$1_0_old Int)
       (res$1_0_old Int)
       (votes$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_2_old Int)
       (i.0$2_0_old Int)
       (length$2_0_old Int)
       (res$2_0_old Int)
       (v$2_0_old Int)
       (votes$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((i.0$1_0 i.0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((res$1_0 res$1_0_old)
                (votes$1_0 votes$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (< i.0$1_0 length$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 (< i.0$1_0 length$1_0)))
                     (=>
                        (not _$1_2)
                        (let
                           ((i.0$1_0 i.0$1_0))
                           (=>
                              (and
                                 (let
                                    ((_$2_2 _$2_2_old)
                                     (i.0$2_0 i.0$2_0_old)
                                     (length$2_0 length$2_0_old))
                                    (let
                                       ((res$2_0 res$2_0_old)
                                        (v$2_0 v$2_0_old)
                                        (votes$2_0 votes$2_0_old)
                                        (w$2_0 w$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (_$2_11 (< i.0$2_0 length$2_0)))
                                       (=>
                                          _$2_11
                                          (let
                                             ((_$2_12 (< i.0$2_0 length$2_0)))
                                             (=>
                                                _$2_12
                                                (let
                                                   ((_$2_13 i.0$2_0))
                                                   (let
                                                      ((_$2_14 (+ votes$2_0 (* 4 _$2_13))))
                                                      (let
                                                         ((_$2_15 (select HEAP$2 _$2_14)))
                                                         (let
                                                            ((_$2_16 _$2_15))
                                                            (let
                                                               ((_$2_17 (+ res$2_0 (* 4 _$2_16))))
                                                               (let
                                                                  ((_$2_18 (select HEAP$2 _$2_17)))
                                                                  (let
                                                                     ((_$2_19 (+ _$2_18 1)))
                                                                     (let
                                                                        ((HEAP$2 (store HEAP$2 _$2_17 _$2_19))
                                                                         (_$2_20 (+ i.0$2_0 1)))
                                                                        (let
                                                                           ((i.0$2_0 _$2_20))
                                                                           false))))))))))))))
                                 (let
                                    ((_$2_2 _$2_2_old)
                                     (i.0$2_0 i.0$2_0_old)
                                     (length$2_0 length$2_0_old))
                                    (let
                                       ((res$2_0 res$2_0_old)
                                        (v$2_0 v$2_0_old)
                                        (votes$2_0 votes$2_0_old)
                                        (w$2_0 w$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (_$2_11 (< i.0$2_0 length$2_0)))
                                       (=>
                                          _$2_11
                                          (let
                                             ((_$2_12 (< i.0$2_0 length$2_0)))
                                             (=>
                                                (not _$2_12)
                                                (let
                                                   ((i.0$2_0 i.0$2_0))
                                                   false)))))))
                              (forall
                                 ((i1 Int)
                                  (i2_old Int))
                                 (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (length$1_0_old Int)
       (res$1_0_old Int)
       (votes$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_2_old Int)
       (i.0$2_0_old Int)
       (length$2_0_old Int)
       (res$2_0_old Int)
       (v$2_0_old Int)
       (votes$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$2_2 _$2_2_old)
             (i.0$2_0 i.0$2_0_old)
             (length$2_0 length$2_0_old))
            (let
               ((res$2_0 res$2_0_old)
                (v$2_0 v$2_0_old)
                (votes$2_0 votes$2_0_old)
                (w$2_0 w$2_0_old)
                (HEAP$2 HEAP$2_old)
                (_$2_11 (< i.0$2_0 length$2_0)))
               (=>
                  _$2_11
                  (let
                     ((_$2_12 (< i.0$2_0 length$2_0)))
                     (=>
                        _$2_12
                        (let
                           ((_$2_13 i.0$2_0))
                           (let
                              ((_$2_14 (+ votes$2_0 (* 4 _$2_13))))
                              (let
                                 ((_$2_15 (select HEAP$2 _$2_14)))
                                 (let
                                    ((_$2_16 _$2_15))
                                    (let
                                       ((_$2_17 (+ res$2_0 (* 4 _$2_16))))
                                       (let
                                          ((_$2_18 (select HEAP$2 _$2_17)))
                                          (let
                                             ((_$2_19 (+ _$2_18 1)))
                                             (let
                                                ((HEAP$2 (store HEAP$2 _$2_17 _$2_19))
                                                 (_$2_20 (+ i.0$2_0 1)))
                                                (let
                                                   ((i.0$2_0 _$2_20))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (length$1_0 length$1_0_old))
                                                            (let
                                                               ((res$1_0 res$1_0_old)
                                                                (votes$1_0 votes$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (_$1_1 (< i.0$1_0 length$1_0)))
                                                               (=>
                                                                  _$1_1
                                                                  (let
                                                                     ((_$1_2 (< i.0$1_0 length$1_0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_3 i.0$1_0))
                                                                           (let
                                                                              ((_$1_4 (+ votes$1_0 (* 4 _$1_3))))
                                                                              (let
                                                                                 ((_$1_5 (select HEAP$1 _$1_4)))
                                                                                 (let
                                                                                    ((_$1_6 _$1_5))
                                                                                    (let
                                                                                       ((_$1_7 (+ res$1_0 (* 4 _$1_6))))
                                                                                       (let
                                                                                          ((_$1_8 (select HEAP$1 _$1_7)))
                                                                                          (let
                                                                                             ((_$1_9 (+ _$1_8 1)))
                                                                                             (let
                                                                                                ((HEAP$1 (store HEAP$1 _$1_7 _$1_9))
                                                                                                 (_$1_10 (+ i.0$1_0 1)))
                                                                                                (let
                                                                                                   ((i.0$1_0 _$1_10))
                                                                                                   false))))))))))))))
                                                         (let
                                                            ((i.0$1_0 i.0$1_0_old)
                                                             (length$1_0 length$1_0_old))
                                                            (let
                                                               ((res$1_0 res$1_0_old)
                                                                (votes$1_0 votes$1_0_old)
                                                                (HEAP$1 HEAP$1_old)
                                                                (_$1_1 (< i.0$1_0 length$1_0)))
                                                               (=>
                                                                  _$1_1
                                                                  (let
                                                                     ((_$1_2 (< i.0$1_0 length$1_0)))
                                                                     (=>
                                                                        (not _$1_2)
                                                                        (let
                                                                           ((i.0$1_0 i.0$1_0))
                                                                           false)))))))
                                                      (forall
                                                         ((i1_old Int)
                                                          (i2 Int))
                                                         (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (length$1_0_old Int)
       (res$1_0_old Int)
       (votes$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_2_old Int)
       (i.0$2_0_old Int)
       (length$2_0_old Int)
       (res$2_0_old Int)
       (v$2_0_old Int)
       (votes$2_0_old Int)
       (w$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2_old i.0$2_0_old length$2_0_old res$2_0_old v$2_0_old votes$2_0_old w$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((_$2_2 _$2_2_old)
             (i.0$2_0 i.0$2_0_old)
             (length$2_0 length$2_0_old))
            (let
               ((res$2_0 res$2_0_old)
                (v$2_0 v$2_0_old)
                (votes$2_0 votes$2_0_old)
                (w$2_0 w$2_0_old)
                (HEAP$2 HEAP$2_old)
                (_$2_11 (< i.0$2_0 length$2_0)))
               (=>
                  _$2_11
                  (let
                     ((_$2_12 (< i.0$2_0 length$2_0)))
                     (=>
                        (not _$2_12)
                        (let
                           ((i.0$2_0 i.0$2_0))
                           (=>
                              (and
                                 (let
                                    ((i.0$1_0 i.0$1_0_old)
                                     (length$1_0 length$1_0_old))
                                    (let
                                       ((res$1_0 res$1_0_old)
                                        (votes$1_0 votes$1_0_old)
                                        (HEAP$1 HEAP$1_old)
                                        (_$1_1 (< i.0$1_0 length$1_0)))
                                       (=>
                                          _$1_1
                                          (let
                                             ((_$1_2 (< i.0$1_0 length$1_0)))
                                             (=>
                                                _$1_2
                                                (let
                                                   ((_$1_3 i.0$1_0))
                                                   (let
                                                      ((_$1_4 (+ votes$1_0 (* 4 _$1_3))))
                                                      (let
                                                         ((_$1_5 (select HEAP$1 _$1_4)))
                                                         (let
                                                            ((_$1_6 _$1_5))
                                                            (let
                                                               ((_$1_7 (+ res$1_0 (* 4 _$1_6))))
                                                               (let
                                                                  ((_$1_8 (select HEAP$1 _$1_7)))
                                                                  (let
                                                                     ((_$1_9 (+ _$1_8 1)))
                                                                     (let
                                                                        ((HEAP$1 (store HEAP$1 _$1_7 _$1_9))
                                                                         (_$1_10 (+ i.0$1_0 1)))
                                                                        (let
                                                                           ((i.0$1_0 _$1_10))
                                                                           false))))))))))))))
                                 (let
                                    ((i.0$1_0 i.0$1_0_old)
                                     (length$1_0 length$1_0_old))
                                    (let
                                       ((res$1_0 res$1_0_old)
                                        (votes$1_0 votes$1_0_old)
                                        (HEAP$1 HEAP$1_old)
                                        (_$1_1 (< i.0$1_0 length$1_0)))
                                       (=>
                                          _$1_1
                                          (let
                                             ((_$1_2 (< i.0$1_0 length$1_0)))
                                             (=>
                                                (not _$1_2)
                                                (let
                                                   ((i.0$1_0 i.0$1_0))
                                                   false)))))))
                              (forall
                                 ((i1_old Int)
                                  (i2 Int))
                                 (INV_MAIN_0 i.0$1_0_old length$1_0_old res$1_0_old votes$1_0_old i1_old (select HEAP$1_old i1_old) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2)))))))))))))
(check-sat)
(get-model)
