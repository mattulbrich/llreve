(define-fun
   IN_INV
   ((x$1_0 Int)
    (n$1_0 Int)
    (a$1_0 Int)
    (b$1_0 Int)
    (HEAP$1 (Array Int Int))
    (x$2_0 Int)
    (n$2_0 Int)
    (a$2_0 Int)
    (b$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= x$1_0 x$2_0)
      (= n$1_0 n$2_0)
      (= a$1_0 a$2_0)
      (= b$1_0 b$2_0)
      (= HEAP$1 HEAP$2)
      (and (>= a$1_0 0) (< b$1_0 n$1_0) (< a$1_0 b$1_0))))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (= HEAP$1 HEAP$2)))
(declare-var
   HEAP$1_old
   (Array Int Int))
(declare-var
   HEAP$2_old
   (Array Int Int))
(declare-var
   a$1_0_old
   Int)
(declare-var
   a$2_0_old
   Int)
(declare-var
   b$1_0_old
   Int)
(declare-var
   b$2_0_old
   Int)
(declare-var
   cnt.0$1_0_old
   Int)
(declare-var
   cnt.0$2_0_old
   Int)
(declare-var
   i.0$1_0_old
   Int)
(declare-var
   i.0$2_0_old
   Int)
(declare-var
   n$1_0_old
   Int)
(declare-var
   n$2_0_old
   Int)
(declare-var
   res.0$1_0_old
   Int)
(declare-var
   res.0$2_0_old
   Int)
(declare-var
   x$1_0_old
   Int)
(declare-var
   x$2_0_old
   Int)
(declare-var
   INV_INDEX
   Int)
(define-fun
   INV_MAIN_1
   ((cnt$1 Int)
    (i$1 Int)
    (n$1 Int)
    (res$1 Int)
    (x$1 Int)
    (heap$1 (Array Int Int))
    (a$2 Int)
    (b$2 Int)
    (cnt$2 Int)
    (i$2 Int)
    (n$2 Int)
    (res$2 Int)
    (x$2 Int)
    (heap$2 (Array Int Int)))
   Bool
   (and
    (= i$1 i$2)
    (= n$1 n$2)
    (= heap$1 heap$2)
    (= x$1 x$2)
    (and (>= a$2 0) (< b$2 n$1) (< a$2 b$2))
    (=> (<= i$1 a$2) (and (= res$1 res$2)
                          (= cnt$1 cnt$2)))
    (=> (< b$2 i$1) (and (= res$1 res$2)
                         (= cnt$1 cnt$2)))
    (=> (and (< a$2 i$1) (<= i$1 b$2))
        (let ((aval (select heap$2 (+ x$1 (* 4 a$2))))
              (bval (select heap$2 (+ x$1 (* 4 b$2)))))
          (and
           (=> (and (> aval 10000) (> bval 10000)) (= cnt$1 cnt$2))
           (=> (and (> aval 10000) (<= bval 10000)) (= cnt$1 (+ 1 cnt$2)))
           (=> (and (<= aval 10000) (> bval 10000)) (= (+ 1 cnt$1) cnt$2))
           (=> (and (<= aval 10000) (<= bval 10000)) (= cnt$1 cnt$2))
           (= res$1 (+ (- (ite (> aval 10000) aval 0) (ite (> bval 10000) bval 0)) res$2)))))))
(assert
   (or
      (and
         (= INV_INDEX -1)
         (not (=>
                  (IN_INV x$1_0_old n$1_0_old a$1_0_old b$1_0_old HEAP$1_old x$2_0_old n$2_0_old a$2_0_old b$2_0_old HEAP$2_old)
                  (let
                     ((x$1_0 x$1_0_old)
                      (n$1_0 n$1_0_old)
                      (a$1_0 a$1_0_old)
                      (b$1_0 b$1_0_old)
                      (HEAP$1 HEAP$1_old)
                      (res.0$1_0 0)
                      (cnt.0$1_0 0)
                      (i.0$1_0 0)
                      (x$2_0 x$2_0_old)
                      (n$2_0 n$2_0_old)
                      (a$2_0 a$2_0_old)
                      (b$2_0 b$2_0_old)
                      (HEAP$2 HEAP$2_old)
                      (res.0$2_0 0)
                      (cnt.0$2_0 0)
                      (i.0$2_0 0))
                     (INV_MAIN_1 cnt.0$1_0 i.0$1_0 n$1_0 res.0$1_0 x$1_0 HEAP$1 a$2_0 b$2_0 cnt.0$2_0 i.0$2_0 n$2_0 res.0$2_0 x$2_0 HEAP$2)))))
      (and
         (= INV_INDEX 1)
         (not (=>
                  (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0_old b$2_0_old cnt.0$2_0_old i.0$2_0_old n$2_0_old res.0$2_0_old x$2_0_old HEAP$2_old)
                  (let
                     ((cnt.0$1_0 cnt.0$1_0_old)
                      (i.0$1_0 i.0$1_0_old)
                      (n$1_0 n$1_0_old))
                     (let
                        ((res.0$1_0 res.0$1_0_old)
                         (x$1_0 x$1_0_old)
                         (HEAP$1 HEAP$1_old)
                         (_$1_0 (< i.0$1_0 n$1_0)))
                        (=>
                           (not _$1_0)
                           (let
                              ((_$1_8 (div res.0$1_0 cnt.0$1_0)))
                              (let
                                 ((result$1 _$1_8)
                                  (HEAP$1_res HEAP$1)
                                  (a$2_0 a$2_0_old)
                                  (b$2_0 b$2_0_old)
                                  (cnt.0$2_0 cnt.0$2_0_old)
                                  (i.0$2_0 i.0$2_0_old)
                                  (n$2_0 n$2_0_old))
                                 (let
                                    ((res.0$2_0 res.0$2_0_old)
                                     (x$2_0 x$2_0_old)
                                     (HEAP$2 HEAP$2_old)
                                     (_$2_0 (< i.0$2_0 n$2_0)))
                                    (=>
                                       (not _$2_0)
                                       (let
                                          ((_$2_17 (div res.0$2_0 cnt.0$2_0)))
                                          (let
                                             ((result$2 _$2_17)
                                              (HEAP$2_res HEAP$2))
                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))
      (and
         (= INV_INDEX 1)
         (not (=>
                  (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0_old b$2_0_old cnt.0$2_0_old i.0$2_0_old n$2_0_old res.0$2_0_old x$2_0_old HEAP$2_old)
                  (let
                     ((cnt.0$1_0 cnt.0$1_0_old)
                      (i.0$1_0 i.0$1_0_old)
                      (n$1_0 n$1_0_old))
                     (let
                        ((res.0$1_0 res.0$1_0_old)
                         (x$1_0 x$1_0_old)
                         (HEAP$1 HEAP$1_old)
                         (_$1_0 (< i.0$1_0 n$1_0)))
                        (=>
                           _$1_0
                           (let
                              ((_$1_1 i.0$1_0))
                              (let
                                 ((_$1_2 (+ x$1_0 (* 4 _$1_1))))
                                 (let
                                    ((_$1_3 (select HEAP$1 _$1_2)))
                                    (let
                                       ((_$1_4 (> _$1_3 10000))
                                        (_$1_5 (+ res.0$1_0 _$1_3))
                                        (_$1_6 (+ cnt.0$1_0 1)))
                                       (let
                                          ((res.1$1_0 (ite _$1_4 _$1_5 res.0$1_0))
                                           (cnt.1$1_0 (ite _$1_4 _$1_6 cnt.0$1_0))
                                           (_$1_7 (+ i.0$1_0 1)))
                                          (let
                                             ((res.0$1_0 res.1$1_0)
                                              (cnt.0$1_0 cnt.1$1_0)
                                              (i.0$1_0 _$1_7)
                                              (a$2_0 a$2_0_old)
                                              (b$2_0 b$2_0_old)
                                              (cnt.0$2_0 cnt.0$2_0_old)
                                              (i.0$2_0 i.0$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (let
                                                ((res.0$2_0 res.0$2_0_old)
                                                 (x$2_0 x$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (_$2_0 (< i.0$2_0 n$2_0)))
                                                (=>
                                                   _$2_0
                                                   (let
                                                      ((_$2_1 (= i.0$2_0 a$2_0)))
                                                      (=>
                                                         _$2_1
                                                         (let
                                                            ((_$2_2 b$2_0))
                                                            (let
                                                               ((_$2_3 (+ x$2_0 (* 4 _$2_2))))
                                                               (let
                                                                  ((_$2_4 (select HEAP$2 _$2_3)))
                                                                  (let
                                                                     ((_$2_12 _$2_4))
                                                                     (let
                                                                        ((_$2_13 (> _$2_12 10000))
                                                                         (_$2_14 (+ res.0$2_0 _$2_12))
                                                                         (_$2_15 (+ cnt.0$2_0 1)))
                                                                        (let
                                                                           ((res.1$2_0 (ite _$2_13 _$2_14 res.0$2_0))
                                                                            (cnt.1$2_0 (ite _$2_13 _$2_15 cnt.0$2_0))
                                                                            (_$2_16 (+ i.0$2_0 1)))
                                                                           (let
                                                                              ((res.0$2_0 res.1$2_0)
                                                                               (cnt.0$2_0 cnt.1$2_0)
                                                                               (i.0$2_0 _$2_16))
                                                                              (INV_MAIN_1 cnt.0$1_0 i.0$1_0 n$1_0 res.0$1_0 x$1_0 HEAP$1 a$2_0 b$2_0 cnt.0$2_0 i.0$2_0 n$2_0 res.0$2_0 x$2_0 HEAP$2))))))))))))))))))))))))
      (and
         (= INV_INDEX 1)
         (not (=>
                  (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0_old b$2_0_old cnt.0$2_0_old i.0$2_0_old n$2_0_old res.0$2_0_old x$2_0_old HEAP$2_old)
                  (let
                     ((cnt.0$1_0 cnt.0$1_0_old)
                      (i.0$1_0 i.0$1_0_old)
                      (n$1_0 n$1_0_old))
                     (let
                        ((res.0$1_0 res.0$1_0_old)
                         (x$1_0 x$1_0_old)
                         (HEAP$1 HEAP$1_old)
                         (_$1_0 (< i.0$1_0 n$1_0)))
                        (=>
                           _$1_0
                           (let
                              ((_$1_1 i.0$1_0))
                              (let
                                 ((_$1_2 (+ x$1_0 (* 4 _$1_1))))
                                 (let
                                    ((_$1_3 (select HEAP$1 _$1_2)))
                                    (let
                                       ((_$1_4 (> _$1_3 10000))
                                        (_$1_5 (+ res.0$1_0 _$1_3))
                                        (_$1_6 (+ cnt.0$1_0 1)))
                                       (let
                                          ((res.1$1_0 (ite _$1_4 _$1_5 res.0$1_0))
                                           (cnt.1$1_0 (ite _$1_4 _$1_6 cnt.0$1_0))
                                           (_$1_7 (+ i.0$1_0 1)))
                                          (let
                                             ((res.0$1_0 res.1$1_0)
                                              (cnt.0$1_0 cnt.1$1_0)
                                              (i.0$1_0 _$1_7)
                                              (a$2_0 a$2_0_old)
                                              (b$2_0 b$2_0_old)
                                              (cnt.0$2_0 cnt.0$2_0_old)
                                              (i.0$2_0 i.0$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (let
                                                ((res.0$2_0 res.0$2_0_old)
                                                 (x$2_0 x$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (_$2_0 (< i.0$2_0 n$2_0)))
                                                (=>
                                                   _$2_0
                                                   (let
                                                      ((_$2_1 (= i.0$2_0 a$2_0)))
                                                      (=>
                                                         (not _$2_1)
                                                         (let
                                                            ((_$2_5 (= i.0$2_0 b$2_0)))
                                                            (=>
                                                               _$2_5
                                                               (let
                                                                  ((_$2_6 a$2_0))
                                                                  (let
                                                                     ((_$2_7 (+ x$2_0 (* 4 _$2_6))))
                                                                     (let
                                                                        ((_$2_8 (select HEAP$2 _$2_7)))
                                                                        (let
                                                                           ((_$2_12 _$2_8))
                                                                           (let
                                                                              ((_$2_13 (> _$2_12 10000))
                                                                               (_$2_14 (+ res.0$2_0 _$2_12))
                                                                               (_$2_15 (+ cnt.0$2_0 1)))
                                                                              (let
                                                                                 ((res.1$2_0 (ite _$2_13 _$2_14 res.0$2_0))
                                                                                  (cnt.1$2_0 (ite _$2_13 _$2_15 cnt.0$2_0))
                                                                                  (_$2_16 (+ i.0$2_0 1)))
                                                                                 (let
                                                                                    ((res.0$2_0 res.1$2_0)
                                                                                     (cnt.0$2_0 cnt.1$2_0)
                                                                                     (i.0$2_0 _$2_16))
                                                                                    (INV_MAIN_1 cnt.0$1_0 i.0$1_0 n$1_0 res.0$1_0 x$1_0 HEAP$1 a$2_0 b$2_0 cnt.0$2_0 i.0$2_0 n$2_0 res.0$2_0 x$2_0 HEAP$2))))))))))))))))))))))))))
      (and
         (= INV_INDEX 1)
         (not (=>
                  (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0_old b$2_0_old cnt.0$2_0_old i.0$2_0_old n$2_0_old res.0$2_0_old x$2_0_old HEAP$2_old)
                  (let
                     ((cnt.0$1_0 cnt.0$1_0_old)
                      (i.0$1_0 i.0$1_0_old)
                      (n$1_0 n$1_0_old))
                     (let
                        ((res.0$1_0 res.0$1_0_old)
                         (x$1_0 x$1_0_old)
                         (HEAP$1 HEAP$1_old)
                         (_$1_0 (< i.0$1_0 n$1_0)))
                        (=>
                           _$1_0
                           (let
                              ((_$1_1 i.0$1_0))
                              (let
                                 ((_$1_2 (+ x$1_0 (* 4 _$1_1))))
                                 (let
                                    ((_$1_3 (select HEAP$1 _$1_2)))
                                    (let
                                       ((_$1_4 (> _$1_3 10000))
                                        (_$1_5 (+ res.0$1_0 _$1_3))
                                        (_$1_6 (+ cnt.0$1_0 1)))
                                       (let
                                          ((res.1$1_0 (ite _$1_4 _$1_5 res.0$1_0))
                                           (cnt.1$1_0 (ite _$1_4 _$1_6 cnt.0$1_0))
                                           (_$1_7 (+ i.0$1_0 1)))
                                          (let
                                             ((res.0$1_0 res.1$1_0)
                                              (cnt.0$1_0 cnt.1$1_0)
                                              (i.0$1_0 _$1_7)
                                              (a$2_0 a$2_0_old)
                                              (b$2_0 b$2_0_old)
                                              (cnt.0$2_0 cnt.0$2_0_old)
                                              (i.0$2_0 i.0$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (let
                                                ((res.0$2_0 res.0$2_0_old)
                                                 (x$2_0 x$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (_$2_0 (< i.0$2_0 n$2_0)))
                                                (=>
                                                   _$2_0
                                                   (let
                                                      ((_$2_1 (= i.0$2_0 a$2_0)))
                                                      (=>
                                                         (not _$2_1)
                                                         (let
                                                            ((_$2_5 (= i.0$2_0 b$2_0)))
                                                            (=>
                                                               (not _$2_5)
                                                               (let
                                                                  ((_$2_9 i.0$2_0))
                                                                  (let
                                                                     ((_$2_10 (+ x$2_0 (* 4 _$2_9))))
                                                                     (let
                                                                        ((_$2_11 (select HEAP$2 _$2_10)))
                                                                        (let
                                                                           ((_$2_12 _$2_11))
                                                                           (let
                                                                              ((_$2_13 (> _$2_12 10000))
                                                                               (_$2_14 (+ res.0$2_0 _$2_12))
                                                                               (_$2_15 (+ cnt.0$2_0 1)))
                                                                              (let
                                                                                 ((res.1$2_0 (ite _$2_13 _$2_14 res.0$2_0))
                                                                                  (cnt.1$2_0 (ite _$2_13 _$2_15 cnt.0$2_0))
                                                                                  (_$2_16 (+ i.0$2_0 1)))
                                                                                 (let
                                                                                    ((res.0$2_0 res.1$2_0)
                                                                                     (cnt.0$2_0 cnt.1$2_0)
                                                                                     (i.0$2_0 _$2_16))
                                                                                    (INV_MAIN_1 cnt.0$1_0 i.0$1_0 n$1_0 res.0$1_0 x$1_0 HEAP$1 a$2_0 b$2_0 cnt.0$2_0 i.0$2_0 n$2_0 res.0$2_0 x$2_0 HEAP$2))))))))))))))))))))))))))
      (and
         (= INV_INDEX 1)
         (not (=>
                  (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0_old b$2_0_old cnt.0$2_0_old i.0$2_0_old n$2_0_old res.0$2_0_old x$2_0_old HEAP$2_old)
                  (let
                     ((cnt.0$1_0 cnt.0$1_0_old)
                      (i.0$1_0 i.0$1_0_old)
                      (n$1_0 n$1_0_old))
                     (let
                        ((res.0$1_0 res.0$1_0_old)
                         (x$1_0 x$1_0_old)
                         (HEAP$1 HEAP$1_old)
                         (_$1_0 (< i.0$1_0 n$1_0)))
                        (=>
                           _$1_0
                           (let
                              ((_$1_1 i.0$1_0))
                              (let
                                 ((_$1_2 (+ x$1_0 (* 4 _$1_1))))
                                 (let
                                    ((_$1_3 (select HEAP$1 _$1_2)))
                                    (let
                                       ((_$1_4 (> _$1_3 10000))
                                        (_$1_5 (+ res.0$1_0 _$1_3))
                                        (_$1_6 (+ cnt.0$1_0 1)))
                                       (let
                                          ((res.1$1_0 (ite _$1_4 _$1_5 res.0$1_0))
                                           (cnt.1$1_0 (ite _$1_4 _$1_6 cnt.0$1_0))
                                           (_$1_7 (+ i.0$1_0 1)))
                                          (let
                                             ((res.0$1_0 res.1$1_0)
                                              (cnt.0$1_0 cnt.1$1_0)
                                              (i.0$1_0 _$1_7))
                                             (=>
                                                (and
                                                   (let
                                                      ((a$2_0 a$2_0_old)
                                                       (b$2_0 b$2_0_old)
                                                       (cnt.0$2_0 cnt.0$2_0_old)
                                                       (i.0$2_0 i.0$2_0_old)
                                                       (n$2_0 n$2_0_old))
                                                      (let
                                                         ((res.0$2_0 res.0$2_0_old)
                                                          (x$2_0 x$2_0_old)
                                                          (HEAP$2 HEAP$2_old)
                                                          (_$2_0 (< i.0$2_0 n$2_0)))
                                                         (=>
                                                            _$2_0
                                                            (let
                                                               ((_$2_1 (= i.0$2_0 a$2_0)))
                                                               (=>
                                                                  _$2_1
                                                                  (let
                                                                     ((_$2_2 b$2_0))
                                                                     (let
                                                                        ((_$2_3 (+ x$2_0 (* 4 _$2_2))))
                                                                        (let
                                                                           ((_$2_4 (select HEAP$2 _$2_3)))
                                                                           (let
                                                                              ((_$2_12 _$2_4))
                                                                              (let
                                                                                 ((_$2_13 (> _$2_12 10000))
                                                                                  (_$2_14 (+ res.0$2_0 _$2_12))
                                                                                  (_$2_15 (+ cnt.0$2_0 1)))
                                                                                 (let
                                                                                    ((res.1$2_0 (ite _$2_13 _$2_14 res.0$2_0))
                                                                                     (cnt.1$2_0 (ite _$2_13 _$2_15 cnt.0$2_0))
                                                                                     (_$2_16 (+ i.0$2_0 1)))
                                                                                    (let
                                                                                       ((res.0$2_0 res.1$2_0)
                                                                                        (cnt.0$2_0 cnt.1$2_0)
                                                                                        (i.0$2_0 _$2_16))
                                                                                       false))))))))))))
                                                   (let
                                                      ((a$2_0 a$2_0_old)
                                                       (b$2_0 b$2_0_old)
                                                       (cnt.0$2_0 cnt.0$2_0_old)
                                                       (i.0$2_0 i.0$2_0_old)
                                                       (n$2_0 n$2_0_old))
                                                      (let
                                                         ((res.0$2_0 res.0$2_0_old)
                                                          (x$2_0 x$2_0_old)
                                                          (HEAP$2 HEAP$2_old)
                                                          (_$2_0 (< i.0$2_0 n$2_0)))
                                                         (=>
                                                            _$2_0
                                                            (let
                                                               ((_$2_1 (= i.0$2_0 a$2_0)))
                                                               (=>
                                                                  (not _$2_1)
                                                                  (let
                                                                     ((_$2_5 (= i.0$2_0 b$2_0)))
                                                                     (=>
                                                                        _$2_5
                                                                        (let
                                                                           ((_$2_6 a$2_0))
                                                                           (let
                                                                              ((_$2_7 (+ x$2_0 (* 4 _$2_6))))
                                                                              (let
                                                                                 ((_$2_8 (select HEAP$2 _$2_7)))
                                                                                 (let
                                                                                    ((_$2_12 _$2_8))
                                                                                    (let
                                                                                       ((_$2_13 (> _$2_12 10000))
                                                                                        (_$2_14 (+ res.0$2_0 _$2_12))
                                                                                        (_$2_15 (+ cnt.0$2_0 1)))
                                                                                       (let
                                                                                          ((res.1$2_0 (ite _$2_13 _$2_14 res.0$2_0))
                                                                                           (cnt.1$2_0 (ite _$2_13 _$2_15 cnt.0$2_0))
                                                                                           (_$2_16 (+ i.0$2_0 1)))
                                                                                          (let
                                                                                             ((res.0$2_0 res.1$2_0)
                                                                                              (cnt.0$2_0 cnt.1$2_0)
                                                                                              (i.0$2_0 _$2_16))
                                                                                             false))))))))))))))
                                                   (let
                                                      ((a$2_0 a$2_0_old)
                                                       (b$2_0 b$2_0_old)
                                                       (cnt.0$2_0 cnt.0$2_0_old)
                                                       (i.0$2_0 i.0$2_0_old)
                                                       (n$2_0 n$2_0_old))
                                                      (let
                                                         ((res.0$2_0 res.0$2_0_old)
                                                          (x$2_0 x$2_0_old)
                                                          (HEAP$2 HEAP$2_old)
                                                          (_$2_0 (< i.0$2_0 n$2_0)))
                                                         (=>
                                                            _$2_0
                                                            (let
                                                               ((_$2_1 (= i.0$2_0 a$2_0)))
                                                               (=>
                                                                  (not _$2_1)
                                                                  (let
                                                                     ((_$2_5 (= i.0$2_0 b$2_0)))
                                                                     (=>
                                                                        (not _$2_5)
                                                                        (let
                                                                           ((_$2_9 i.0$2_0))
                                                                           (let
                                                                              ((_$2_10 (+ x$2_0 (* 4 _$2_9))))
                                                                              (let
                                                                                 ((_$2_11 (select HEAP$2 _$2_10)))
                                                                                 (let
                                                                                    ((_$2_12 _$2_11))
                                                                                    (let
                                                                                       ((_$2_13 (> _$2_12 10000))
                                                                                        (_$2_14 (+ res.0$2_0 _$2_12))
                                                                                        (_$2_15 (+ cnt.0$2_0 1)))
                                                                                       (let
                                                                                          ((res.1$2_0 (ite _$2_13 _$2_14 res.0$2_0))
                                                                                           (cnt.1$2_0 (ite _$2_13 _$2_15 cnt.0$2_0))
                                                                                           (_$2_16 (+ i.0$2_0 1)))
                                                                                          (let
                                                                                             ((res.0$2_0 res.1$2_0)
                                                                                              (cnt.0$2_0 cnt.1$2_0)
                                                                                              (i.0$2_0 _$2_16))
                                                                                             false)))))))))))))))
                                                (INV_MAIN_1 cnt.0$1_0 i.0$1_0 n$1_0 res.0$1_0 x$1_0 HEAP$1 a$2_0_old b$2_0_old cnt.0$2_0_old i.0$2_0_old n$2_0_old res.0$2_0_old x$2_0_old HEAP$2_old))))))))))))))
      (and
         (= INV_INDEX 1)
         (not (=>
                  (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0_old b$2_0_old cnt.0$2_0_old i.0$2_0_old n$2_0_old res.0$2_0_old x$2_0_old HEAP$2_old)
                  (let
                     ((a$2_0 a$2_0_old)
                      (b$2_0 b$2_0_old)
                      (cnt.0$2_0 cnt.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old)
                      (n$2_0 n$2_0_old))
                     (let
                        ((res.0$2_0 res.0$2_0_old)
                         (x$2_0 x$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (_$2_0 (< i.0$2_0 n$2_0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= i.0$2_0 a$2_0)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_2 b$2_0))
                                    (let
                                       ((_$2_3 (+ x$2_0 (* 4 _$2_2))))
                                       (let
                                          ((_$2_4 (select HEAP$2 _$2_3)))
                                          (let
                                             ((_$2_12 _$2_4))
                                             (let
                                                ((_$2_13 (> _$2_12 10000))
                                                 (_$2_14 (+ res.0$2_0 _$2_12))
                                                 (_$2_15 (+ cnt.0$2_0 1)))
                                                (let
                                                   ((res.1$2_0 (ite _$2_13 _$2_14 res.0$2_0))
                                                    (cnt.1$2_0 (ite _$2_13 _$2_15 cnt.0$2_0))
                                                    (_$2_16 (+ i.0$2_0 1)))
                                                   (let
                                                      ((res.0$2_0 res.1$2_0)
                                                       (cnt.0$2_0 cnt.1$2_0)
                                                       (i.0$2_0 _$2_16))
                                                      (=>
                                                         (and
                                                            (let
                                                               ((cnt.0$1_0 cnt.0$1_0_old)
                                                                (i.0$1_0 i.0$1_0_old)
                                                                (n$1_0 n$1_0_old))
                                                               (let
                                                                  ((res.0$1_0 res.0$1_0_old)
                                                                   (x$1_0 x$1_0_old)
                                                                   (HEAP$1 HEAP$1_old)
                                                                   (_$1_0 (< i.0$1_0 n$1_0)))
                                                                  (=>
                                                                     _$1_0
                                                                     (let
                                                                        ((_$1_1 i.0$1_0))
                                                                        (let
                                                                           ((_$1_2 (+ x$1_0 (* 4 _$1_1))))
                                                                           (let
                                                                              ((_$1_3 (select HEAP$1 _$1_2)))
                                                                              (let
                                                                                 ((_$1_4 (> _$1_3 10000))
                                                                                  (_$1_5 (+ res.0$1_0 _$1_3))
                                                                                  (_$1_6 (+ cnt.0$1_0 1)))
                                                                                 (let
                                                                                    ((res.1$1_0 (ite _$1_4 _$1_5 res.0$1_0))
                                                                                     (cnt.1$1_0 (ite _$1_4 _$1_6 cnt.0$1_0))
                                                                                     (_$1_7 (+ i.0$1_0 1)))
                                                                                    (let
                                                                                       ((res.0$1_0 res.1$1_0)
                                                                                        (cnt.0$1_0 cnt.1$1_0)
                                                                                        (i.0$1_0 _$1_7))
                                                                                       false))))))))))
                                                         (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0 b$2_0 cnt.0$2_0 i.0$2_0 n$2_0 res.0$2_0 x$2_0 HEAP$2)))))))))))))))))
      (and
         (= INV_INDEX 1)
         (not (=>
                  (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0_old b$2_0_old cnt.0$2_0_old i.0$2_0_old n$2_0_old res.0$2_0_old x$2_0_old HEAP$2_old)
                  (let
                     ((a$2_0 a$2_0_old)
                      (b$2_0 b$2_0_old)
                      (cnt.0$2_0 cnt.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old)
                      (n$2_0 n$2_0_old))
                     (let
                        ((res.0$2_0 res.0$2_0_old)
                         (x$2_0 x$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (_$2_0 (< i.0$2_0 n$2_0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= i.0$2_0 a$2_0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_5 (= i.0$2_0 b$2_0)))
                                    (=>
                                       _$2_5
                                       (let
                                          ((_$2_6 a$2_0))
                                          (let
                                             ((_$2_7 (+ x$2_0 (* 4 _$2_6))))
                                             (let
                                                ((_$2_8 (select HEAP$2 _$2_7)))
                                                (let
                                                   ((_$2_12 _$2_8))
                                                   (let
                                                      ((_$2_13 (> _$2_12 10000))
                                                       (_$2_14 (+ res.0$2_0 _$2_12))
                                                       (_$2_15 (+ cnt.0$2_0 1)))
                                                      (let
                                                         ((res.1$2_0 (ite _$2_13 _$2_14 res.0$2_0))
                                                          (cnt.1$2_0 (ite _$2_13 _$2_15 cnt.0$2_0))
                                                          (_$2_16 (+ i.0$2_0 1)))
                                                         (let
                                                            ((res.0$2_0 res.1$2_0)
                                                             (cnt.0$2_0 cnt.1$2_0)
                                                             (i.0$2_0 _$2_16))
                                                            (=>
                                                               (and
                                                                  (let
                                                                     ((cnt.0$1_0 cnt.0$1_0_old)
                                                                      (i.0$1_0 i.0$1_0_old)
                                                                      (n$1_0 n$1_0_old))
                                                                     (let
                                                                        ((res.0$1_0 res.0$1_0_old)
                                                                         (x$1_0 x$1_0_old)
                                                                         (HEAP$1 HEAP$1_old)
                                                                         (_$1_0 (< i.0$1_0 n$1_0)))
                                                                        (=>
                                                                           _$1_0
                                                                           (let
                                                                              ((_$1_1 i.0$1_0))
                                                                              (let
                                                                                 ((_$1_2 (+ x$1_0 (* 4 _$1_1))))
                                                                                 (let
                                                                                    ((_$1_3 (select HEAP$1 _$1_2)))
                                                                                    (let
                                                                                       ((_$1_4 (> _$1_3 10000))
                                                                                        (_$1_5 (+ res.0$1_0 _$1_3))
                                                                                        (_$1_6 (+ cnt.0$1_0 1)))
                                                                                       (let
                                                                                          ((res.1$1_0 (ite _$1_4 _$1_5 res.0$1_0))
                                                                                           (cnt.1$1_0 (ite _$1_4 _$1_6 cnt.0$1_0))
                                                                                           (_$1_7 (+ i.0$1_0 1)))
                                                                                          (let
                                                                                             ((res.0$1_0 res.1$1_0)
                                                                                              (cnt.0$1_0 cnt.1$1_0)
                                                                                              (i.0$1_0 _$1_7))
                                                                                             false))))))))))
                                                               (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0 b$2_0 cnt.0$2_0 i.0$2_0 n$2_0 res.0$2_0 x$2_0 HEAP$2)))))))))))))))))))
      (and
         (= INV_INDEX 1)
         (not (=>
                  (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0_old b$2_0_old cnt.0$2_0_old i.0$2_0_old n$2_0_old res.0$2_0_old x$2_0_old HEAP$2_old)
                  (let
                     ((a$2_0 a$2_0_old)
                      (b$2_0 b$2_0_old)
                      (cnt.0$2_0 cnt.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old)
                      (n$2_0 n$2_0_old))
                     (let
                        ((res.0$2_0 res.0$2_0_old)
                         (x$2_0 x$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (_$2_0 (< i.0$2_0 n$2_0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= i.0$2_0 a$2_0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_5 (= i.0$2_0 b$2_0)))
                                    (=>
                                       (not _$2_5)
                                       (let
                                          ((_$2_9 i.0$2_0))
                                          (let
                                             ((_$2_10 (+ x$2_0 (* 4 _$2_9))))
                                             (let
                                                ((_$2_11 (select HEAP$2 _$2_10)))
                                                (let
                                                   ((_$2_12 _$2_11))
                                                   (let
                                                      ((_$2_13 (> _$2_12 10000))
                                                       (_$2_14 (+ res.0$2_0 _$2_12))
                                                       (_$2_15 (+ cnt.0$2_0 1)))
                                                      (let
                                                         ((res.1$2_0 (ite _$2_13 _$2_14 res.0$2_0))
                                                          (cnt.1$2_0 (ite _$2_13 _$2_15 cnt.0$2_0))
                                                          (_$2_16 (+ i.0$2_0 1)))
                                                         (let
                                                            ((res.0$2_0 res.1$2_0)
                                                             (cnt.0$2_0 cnt.1$2_0)
                                                             (i.0$2_0 _$2_16))
                                                            (=>
                                                               (and
                                                                  (let
                                                                     ((cnt.0$1_0 cnt.0$1_0_old)
                                                                      (i.0$1_0 i.0$1_0_old)
                                                                      (n$1_0 n$1_0_old))
                                                                     (let
                                                                        ((res.0$1_0 res.0$1_0_old)
                                                                         (x$1_0 x$1_0_old)
                                                                         (HEAP$1 HEAP$1_old)
                                                                         (_$1_0 (< i.0$1_0 n$1_0)))
                                                                        (=>
                                                                           _$1_0
                                                                           (let
                                                                              ((_$1_1 i.0$1_0))
                                                                              (let
                                                                                 ((_$1_2 (+ x$1_0 (* 4 _$1_1))))
                                                                                 (let
                                                                                    ((_$1_3 (select HEAP$1 _$1_2)))
                                                                                    (let
                                                                                       ((_$1_4 (> _$1_3 10000))
                                                                                        (_$1_5 (+ res.0$1_0 _$1_3))
                                                                                        (_$1_6 (+ cnt.0$1_0 1)))
                                                                                       (let
                                                                                          ((res.1$1_0 (ite _$1_4 _$1_5 res.0$1_0))
                                                                                           (cnt.1$1_0 (ite _$1_4 _$1_6 cnt.0$1_0))
                                                                                           (_$1_7 (+ i.0$1_0 1)))
                                                                                          (let
                                                                                             ((res.0$1_0 res.1$1_0)
                                                                                              (cnt.0$1_0 cnt.1$1_0)
                                                                                              (i.0$1_0 _$1_7))
                                                                                             false))))))))))
                                                               (INV_MAIN_1 cnt.0$1_0_old i.0$1_0_old n$1_0_old res.0$1_0_old x$1_0_old HEAP$1_old a$2_0 b$2_0 cnt.0$2_0 i.0$2_0 n$2_0 res.0$2_0 x$2_0 HEAP$2)))))))))))))))))))))
(check-sat)
(get-model)
