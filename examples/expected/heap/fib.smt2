(set-logic HORN)
(define-fun
   IN_INV
   ((n$1_0 Int)
    (x$1_0 Int)
    (n$2_0 Int)
    (a$2_0 Int))
   Bool
   (and (= n$1_0 n$2_0) (= x$1_0 a$2_0) (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i))) (>= n$1_0 0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(declare-fun
   INV_42_MAIN
   (Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_fib
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_fib_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_fib__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_fib__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_fib__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_fib__2_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_42
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42_PRE
   (Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1
   (Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__2
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__2_PRE
   (Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((n$1_0_old Int)
       (x$1_0_old Int)
       (n$2_0_old Int)
       (a$2_0_old Int))
      (=>
         (IN_INV
            n$1_0_old
            x$1_0_old
            n$2_0_old
            a$2_0_old)
         (let
            ((i.0$1_0 2)
             (a.0$1_0 1)
             (b.0$1_0 1)
             (n$1_0 n$1_0_old)
             (_$2_0 (+ a$2_0_old 0)))
            (let
               ((HEAP$2 (store HEAP$2_old _$2_0 1))
                (_$2_1 (+ a$2_0_old 1)))
               (let
                  ((HEAP$2 (store HEAP$2 _$2_1 1))
                   (i.0$2_0 2)
                   (a$2_0 a$2_0_old)
                   (n$2_0 n$2_0_old))
                  (INV_42_MAIN a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0)))))))
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 b.0$1_0_old)
                   (_$2_3 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_3)
                     (let
                        ((_$2_19 (- i.0$2_0_old 1)))
                        (let
                           ((_$2_20 _$2_19))
                           (let
                              ((_$2_21 (+ a$2_0_old _$2_20)))
                              (let
                                 ((_$2_22 (select HEAP$2_old _$2_21)))
                                 (let
                                    ((result$2 _$2_22))
                                    (OUT_INV
                                       result$1
                                       result$2)))))))))))))
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ b.0$1_0_old a.0$1_0_old))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (a.0$1_0 b.0$1_0_old)
                      (b.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old)
                      (_$2_3 (< i.0$2_0_old n$2_0_old)))
                     (=>
                        _$2_3
                        (let
                           ((_$2_7 (- i.0$2_0_old 1)))
                           (let
                              ((_$2_8 _$2_7))
                              (let
                                 ((_$2_9 (+ a$2_0_old _$2_8)))
                                 (let
                                    ((_$2_10 (select HEAP$2_old _$2_9))
                                     (_$2_11 (- i.0$2_0_old 2)))
                                    (let
                                       ((_$2_12 _$2_11))
                                       (let
                                          ((_$2_13 (+ a$2_0_old _$2_12)))
                                          (let
                                             ((_$2_14 (select HEAP$2_old _$2_13)))
                                             (let
                                                ((_$2_15 (+ _$2_10 _$2_14))
                                                 (_$2_16 i.0$2_0_old))
                                                (let
                                                   ((_$2_17 (+ a$2_0_old _$2_16)))
                                                   (let
                                                      ((HEAP$2 (store HEAP$2_old _$2_17 _$2_15))
                                                       (_$2_18 (+ i.0$2_0_old 1)))
                                                      (let
                                                         ((i.0$2_0 _$2_18)
                                                          (a$2_0 a$2_0_old)
                                                          (n$2_0 n$2_0_old))
                                                         (INV_42_MAIN a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0))))))))))))))))))))
; forbidden main
; offbyn main
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ b.0$1_0_old a.0$1_0_old))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (a.0$1_0 b.0$1_0_old)
                      (b.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                              (=>
                                 _$2_3
                                 (let
                                    ((_$2_7 (- i.0$2_0_old 1)))
                                    (let
                                       ((_$2_8 _$2_7))
                                       (let
                                          ((_$2_9 (+ a$2_0_old _$2_8)))
                                          (let
                                             ((_$2_10 (select HEAP$2_old _$2_9))
                                              (_$2_11 (- i.0$2_0_old 2)))
                                             (let
                                                ((_$2_12 _$2_11))
                                                (let
                                                   ((_$2_13 (+ a$2_0_old _$2_12)))
                                                   (let
                                                      ((_$2_14 (select HEAP$2_old _$2_13)))
                                                      (let
                                                         ((_$2_15 (+ _$2_10 _$2_14))
                                                          (_$2_16 i.0$2_0_old))
                                                         (let
                                                            ((_$2_17 (+ a$2_0_old _$2_16)))
                                                            (let
                                                               ((HEAP$2 (store HEAP$2_old _$2_17 _$2_15))
                                                                (_$2_18 (+ i.0$2_0_old 1)))
                                                               (let
                                                                  ((i.0$2_0 _$2_18)
                                                                   (a$2_0 a$2_0_old)
                                                                   (n$2_0 n$2_0_old))
                                                                  false))))))))))))))
                        (INV_42_MAIN a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 a$2_0_old i.0$2_0_old n$2_0_old)))))))))
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (- i.0$2_0_old 1)))
                  (let
                     ((_$2_8 _$2_7))
                     (let
                        ((_$2_9 (+ a$2_0_old _$2_8)))
                        (let
                           ((_$2_10 (select HEAP$2_old _$2_9))
                            (_$2_11 (- i.0$2_0_old 2)))
                           (let
                              ((_$2_12 _$2_11))
                              (let
                                 ((_$2_13 (+ a$2_0_old _$2_12)))
                                 (let
                                    ((_$2_14 (select HEAP$2_old _$2_13)))
                                    (let
                                       ((_$2_15 (+ _$2_10 _$2_14))
                                        (_$2_16 i.0$2_0_old))
                                       (let
                                          ((_$2_17 (+ a$2_0_old _$2_16)))
                                          (let
                                             ((HEAP$2 (store HEAP$2_old _$2_17 _$2_15))
                                              (_$2_18 (+ i.0$2_0_old 1)))
                                             (let
                                                ((i.0$2_0 _$2_18)
                                                 (a$2_0 a$2_0_old)
                                                 (n$2_0 n$2_0_old))
                                                (=>
                                                   (and
                                                      (let
                                                         ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                                         (=>
                                                            _$1_1
                                                            (let
                                                               ((_$1_5 (+ b.0$1_0_old a.0$1_0_old))
                                                                (_$1_6 (+ i.0$1_0_old 1)))
                                                               (let
                                                                  ((i.0$1_0 _$1_6)
                                                                   (a.0$1_0 b.0$1_0_old)
                                                                   (b.0$1_0 _$1_5)
                                                                   (n$1_0 n$1_0_old))
                                                                  false)))))
                                                   (INV_42_MAIN a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0 i.0$2_0 n$2_0))))))))))))))))))
; end
(assert
   (forall
      ((n$1_0_old Int)
       (x$1_0_old Int)
       (n$2_0_old Int)
       (a$2_0_old Int))
      (=>
         (INV_REC_fib_PRE n$1_0_old x$1_0_old n$2_0_old a$2_0_old)
         (let
            ((i.0$1_0 2)
             (a.0$1_0 1)
             (b.0$1_0 1)
             (n$1_0 n$1_0_old)
             (_$2_0 (+ a$2_0_old 0)))
            (let
               ((HEAP$2 (store HEAP$2_old _$2_0 1))
                (_$2_1 (+ a$2_0_old 1)))
               (let
                  ((HEAP$2 (store HEAP$2 _$2_1 1))
                   (i.0$2_0 2)
                   (a$2_0 a$2_0_old)
                   (n$2_0 n$2_0_old))
                  (forall
                     ((result$1 Int)
                      (result$2 Int))
                     (and
                        (INV_42_PRE a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0)
                        (=>
                           (INV_42 a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0 result$1 result$2)
                           (INV_REC_fib n$1_0_old x$1_0_old n$2_0_old a$2_0_old result$1 result$2))))))))))
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 b.0$1_0_old)
                   (_$2_3 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_3)
                     (let
                        ((_$2_19 (- i.0$2_0_old 1)))
                        (let
                           ((_$2_20 _$2_19))
                           (let
                              ((_$2_21 (+ a$2_0_old _$2_20)))
                              (let
                                 ((_$2_22 (select HEAP$2_old _$2_21)))
                                 (let
                                    ((result$2 _$2_22))
                                    (INV_42 a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ b.0$1_0_old a.0$1_0_old))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (a.0$1_0 b.0$1_0_old)
                      (b.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old)
                      (_$2_3 (< i.0$2_0_old n$2_0_old)))
                     (=>
                        _$2_3
                        (let
                           ((_$2_7 (- i.0$2_0_old 1)))
                           (let
                              ((_$2_8 _$2_7))
                              (let
                                 ((_$2_9 (+ a$2_0_old _$2_8)))
                                 (let
                                    ((_$2_10 (select HEAP$2_old _$2_9))
                                     (_$2_11 (- i.0$2_0_old 2)))
                                    (let
                                       ((_$2_12 _$2_11))
                                       (let
                                          ((_$2_13 (+ a$2_0_old _$2_12)))
                                          (let
                                             ((_$2_14 (select HEAP$2_old _$2_13)))
                                             (let
                                                ((_$2_15 (+ _$2_10 _$2_14))
                                                 (_$2_16 i.0$2_0_old))
                                                (let
                                                   ((_$2_17 (+ a$2_0_old _$2_16)))
                                                   (let
                                                      ((HEAP$2 (store HEAP$2_old _$2_17 _$2_15))
                                                       (_$2_18 (+ i.0$2_0_old 1)))
                                                      (let
                                                         ((i.0$2_0 _$2_18)
                                                          (a$2_0 a$2_0_old)
                                                          (n$2_0 n$2_0_old))
                                                         (forall
                                                            ((result$1 Int)
                                                             (result$2 Int))
                                                            (and
                                                               (INV_42_PRE a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0)
                                                               (=>
                                                                  (INV_42 a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0 result$1 result$2)
                                                                  (INV_42 a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (x$1_0_old Int))
      (=>
         (INV_REC_fib__1_PRE n$1_0_old x$1_0_old)
         (let
            ((i.0$1_0 2)
             (a.0$1_0 1)
             (b.0$1_0 1)
             (n$1_0 n$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_42__1 a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 result$1)
                  (INV_REC_fib__1 n$1_0_old x$1_0_old result$1)))))))
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 b.0$1_0_old))
                  (INV_42__1 a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old result$1)))))))
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ b.0$1_0_old a.0$1_0_old))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (a.0$1_0 b.0$1_0_old)
                      (b.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_42__1 a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 result$1)
                           (INV_42__1 a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old result$1))))))))))
(assert
   (forall
      ((n$2_0_old Int)
       (a$2_0_old Int))
      (=>
         (INV_REC_fib__2_PRE n$2_0_old a$2_0_old)
         (let
            ((_$2_0 (+ a$2_0_old 0)))
            (let
               ((HEAP$2 (store HEAP$2_old _$2_0 1))
                (_$2_1 (+ a$2_0_old 1)))
               (let
                  ((HEAP$2 (store HEAP$2 _$2_1 1))
                   (i.0$2_0 2)
                   (a$2_0 a$2_0_old)
                   (n$2_0 n$2_0_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_42__2 a$2_0 i.0$2_0 n$2_0 result$2)
                        (INV_REC_fib__2 n$2_0_old a$2_0_old result$2)))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               (not _$2_3)
               (let
                  ((_$2_19 (- i.0$2_0_old 1)))
                  (let
                     ((_$2_20 _$2_19))
                     (let
                        ((_$2_21 (+ a$2_0_old _$2_20)))
                        (let
                           ((_$2_22 (select HEAP$2_old _$2_21)))
                           (let
                              ((result$2 _$2_22))
                              (INV_42__2 a$2_0_old i.0$2_0_old n$2_0_old result$2)))))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (- i.0$2_0_old 1)))
                  (let
                     ((_$2_8 _$2_7))
                     (let
                        ((_$2_9 (+ a$2_0_old _$2_8)))
                        (let
                           ((_$2_10 (select HEAP$2_old _$2_9))
                            (_$2_11 (- i.0$2_0_old 2)))
                           (let
                              ((_$2_12 _$2_11))
                              (let
                                 ((_$2_13 (+ a$2_0_old _$2_12)))
                                 (let
                                    ((_$2_14 (select HEAP$2_old _$2_13)))
                                    (let
                                       ((_$2_15 (+ _$2_10 _$2_14))
                                        (_$2_16 i.0$2_0_old))
                                       (let
                                          ((_$2_17 (+ a$2_0_old _$2_16)))
                                          (let
                                             ((HEAP$2 (store HEAP$2_old _$2_17 _$2_15))
                                              (_$2_18 (+ i.0$2_0_old 1)))
                                             (let
                                                ((i.0$2_0 _$2_18)
                                                 (a$2_0 a$2_0_old)
                                                 (n$2_0 n$2_0_old))
                                                (forall
                                                   ((result$2 Int))
                                                   (=>
                                                      (INV_42__2 a$2_0 i.0$2_0 n$2_0 result$2)
                                                      (INV_42__2 a$2_0_old i.0$2_0_old n$2_0_old result$2)))))))))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ b.0$1_0_old a.0$1_0_old))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (a.0$1_0 b.0$1_0_old)
                      (b.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                              (=>
                                 _$2_3
                                 (let
                                    ((_$2_7 (- i.0$2_0_old 1)))
                                    (let
                                       ((_$2_8 _$2_7))
                                       (let
                                          ((_$2_9 (+ a$2_0_old _$2_8)))
                                          (let
                                             ((_$2_10 (select HEAP$2_old _$2_9))
                                              (_$2_11 (- i.0$2_0_old 2)))
                                             (let
                                                ((_$2_12 _$2_11))
                                                (let
                                                   ((_$2_13 (+ a$2_0_old _$2_12)))
                                                   (let
                                                      ((_$2_14 (select HEAP$2_old _$2_13)))
                                                      (let
                                                         ((_$2_15 (+ _$2_10 _$2_14))
                                                          (_$2_16 i.0$2_0_old))
                                                         (let
                                                            ((_$2_17 (+ a$2_0_old _$2_16)))
                                                            (let
                                                               ((HEAP$2 (store HEAP$2_old _$2_17 _$2_15))
                                                                (_$2_18 (+ i.0$2_0_old 1)))
                                                               (let
                                                                  ((i.0$2_0 _$2_18)
                                                                   (a$2_0 a$2_0_old)
                                                                   (n$2_0 n$2_0_old))
                                                                  false))))))))))))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_42_PRE a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 a$2_0_old i.0$2_0_old n$2_0_old)
                              (=>
                                 (INV_42 a.0$1_0 b.0$1_0 i.0$1_0 n$1_0 a$2_0_old i.0$2_0_old n$2_0_old result$1 result$2)
                                 (INV_42 a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((a.0$1_0_old Int)
       (b.0$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (- i.0$2_0_old 1)))
                  (let
                     ((_$2_8 _$2_7))
                     (let
                        ((_$2_9 (+ a$2_0_old _$2_8)))
                        (let
                           ((_$2_10 (select HEAP$2_old _$2_9))
                            (_$2_11 (- i.0$2_0_old 2)))
                           (let
                              ((_$2_12 _$2_11))
                              (let
                                 ((_$2_13 (+ a$2_0_old _$2_12)))
                                 (let
                                    ((_$2_14 (select HEAP$2_old _$2_13)))
                                    (let
                                       ((_$2_15 (+ _$2_10 _$2_14))
                                        (_$2_16 i.0$2_0_old))
                                       (let
                                          ((_$2_17 (+ a$2_0_old _$2_16)))
                                          (let
                                             ((HEAP$2 (store HEAP$2_old _$2_17 _$2_15))
                                              (_$2_18 (+ i.0$2_0_old 1)))
                                             (let
                                                ((i.0$2_0 _$2_18)
                                                 (a$2_0 a$2_0_old)
                                                 (n$2_0 n$2_0_old))
                                                (=>
                                                   (and
                                                      (let
                                                         ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                                         (=>
                                                            _$1_1
                                                            (let
                                                               ((_$1_5 (+ b.0$1_0_old a.0$1_0_old))
                                                                (_$1_6 (+ i.0$1_0_old 1)))
                                                               (let
                                                                  ((i.0$1_0 _$1_6)
                                                                   (a.0$1_0 b.0$1_0_old)
                                                                   (b.0$1_0 _$1_5)
                                                                   (n$1_0 n$1_0_old))
                                                                  false)))))
                                                   (forall
                                                      ((result$1 Int)
                                                       (result$2 Int))
                                                      (and
                                                         (INV_42_PRE a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0 i.0$2_0 n$2_0)
                                                         (=>
                                                            (INV_42 a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0 i.0$2_0 n$2_0 result$1 result$2)
                                                            (INV_42 a.0$1_0_old b.0$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))
(check-sat)
(get-model)
