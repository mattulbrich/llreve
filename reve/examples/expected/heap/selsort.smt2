(set-logic HORN)
(define-fun
   IN_INV
   ((a$1_0 Int)
    (n$1_0 Int)
    (a$2_0 Int)
    (n$2_0 Int))
   Bool
   (and
      (= a$1_0 a$2_0)
      (= n$1_0 n$2_0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(declare-fun
   INV_1_MAIN
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_2_MAIN
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_selsort
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_selsort_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_selsort__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_selsort__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_selsort__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_selsort__2_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_1
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_1_PRE
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_2
   (Int
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
(declare-fun
   INV_2_PRE
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_1__1
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_1__1_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_2__1
   (Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_2__1_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_1__2
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_1__2_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_2__2
   (Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_2__2_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((a$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            a$1_0_old
            n$1_0_old
            a$2_0_old
            n$2_0_old)
         (let
            ((i.0$1_0 0)
             (a$1_0 a$1_0_old)
             (n$1_0 n$1_0_old)
             (i.0$2_0 0)
             (a$2_0 a$2_0_old)
             (n$2_0 n$2_0_old))
            (INV_1_MAIN a$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0)))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1_MAIN a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 0)
                   (_$2_1 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_1)
                     (let
                        ((result$2 0))
                        (OUT_INV
                           result$1
                           result$2)))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1_MAIN a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((j.0$1_0 i.0$1_0_old)
                   (a$1_0 a$1_0_old)
                   (i.0$1_0 i.0$1_0_old)
                   (n$1_0 n$1_0_old)
                   (_$2_1 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     _$2_1
                     (let
                        ((j.0$2_0 i.0$2_0_old)
                         (a$2_0 a$2_0_old)
                         (i.0$2_0 i.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (INV_2_MAIN a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_6)
               (let
                  ((_$1_28 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_28)
                      (a$1_0 a$1_0_old)
                      (n$1_0 n$1_0_old)
                      (_$2_6 (< j.0$2_0_old n$2_0_old)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_28 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_28)
                               (a$2_0 a$2_0_old)
                               (n$2_0 n$2_0_old))
                              (INV_1_MAIN a$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0)))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    _$1_16
                                    (let
                                       ((_$1_17 i.0$1_0_old))
                                       (let
                                          ((_$1_18 (+ a$1_0_old _$1_17)))
                                          (let
                                             ((_$1_19 (select HEAP$1_old _$1_18))
                                              (_$1_20 j.0$1_0_old))
                                             (let
                                                ((_$1_21 (+ a$1_0_old _$1_20)))
                                                (let
                                                   ((_$1_22 (select HEAP$1_old _$1_21))
                                                    (_$1_23 i.0$1_0_old))
                                                   (let
                                                      ((_$1_24 (+ a$1_0_old _$1_23)))
                                                      (let
                                                         ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                          (_$1_25 j.0$1_0_old))
                                                         (let
                                                            ((_$1_26 (+ a$1_0_old _$1_25)))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                (_$1_27 (+ j.0$1_0_old 1)))
                                                               (let
                                                                  ((j.0$1_0 _$1_27)
                                                                   (a$1_0 a$1_0_old)
                                                                   (i.0$1_0 i.0$1_0_old)
                                                                   (n$1_0 n$1_0_old)
                                                                   (_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                                  (=>
                                                                     _$2_6
                                                                     (let
                                                                        ((_$2_10 j.0$2_0_old))
                                                                        (let
                                                                           ((_$2_11 (+ a$2_0_old _$2_10)))
                                                                           (let
                                                                              ((_$2_12 (select HEAP$2_old _$2_11))
                                                                               (_$2_13 i.0$2_0_old))
                                                                              (let
                                                                                 ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                                 (let
                                                                                    ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                                    (let
                                                                                       ((_$2_16 (< _$2_12 _$2_15)))
                                                                                       (=>
                                                                                          _$2_16
                                                                                          (let
                                                                                             ((_$2_17 i.0$2_0_old))
                                                                                             (let
                                                                                                ((_$2_18 (+ a$2_0_old _$2_17)))
                                                                                                (let
                                                                                                   ((_$2_19 (select HEAP$2_old _$2_18))
                                                                                                    (_$2_20 j.0$2_0_old))
                                                                                                   (let
                                                                                                      ((_$2_21 (+ a$2_0_old _$2_20)))
                                                                                                      (let
                                                                                                         ((_$2_22 (select HEAP$2_old _$2_21))
                                                                                                          (_$2_23 i.0$2_0_old))
                                                                                                         (let
                                                                                                            ((_$2_24 (+ a$2_0_old _$2_23)))
                                                                                                            (let
                                                                                                               ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                                                                                (_$2_25 j.0$2_0_old))
                                                                                                               (let
                                                                                                                  ((_$2_26 (+ a$2_0_old _$2_25)))
                                                                                                                  (let
                                                                                                                     ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                                                                      (_$2_27 (+ j.0$2_0_old 1)))
                                                                                                                     (let
                                                                                                                        ((j.0$2_0 _$2_27)
                                                                                                                         (a$2_0 a$2_0_old)
                                                                                                                         (i.0$2_0 i.0$2_0_old)
                                                                                                                         (n$2_0 n$2_0_old))
                                                                                                                        (INV_2_MAIN a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    _$1_16
                                    (let
                                       ((_$1_17 i.0$1_0_old))
                                       (let
                                          ((_$1_18 (+ a$1_0_old _$1_17)))
                                          (let
                                             ((_$1_19 (select HEAP$1_old _$1_18))
                                              (_$1_20 j.0$1_0_old))
                                             (let
                                                ((_$1_21 (+ a$1_0_old _$1_20)))
                                                (let
                                                   ((_$1_22 (select HEAP$1_old _$1_21))
                                                    (_$1_23 i.0$1_0_old))
                                                   (let
                                                      ((_$1_24 (+ a$1_0_old _$1_23)))
                                                      (let
                                                         ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                          (_$1_25 j.0$1_0_old))
                                                         (let
                                                            ((_$1_26 (+ a$1_0_old _$1_25)))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                (_$1_27 (+ j.0$1_0_old 1)))
                                                               (let
                                                                  ((j.0$1_0 _$1_27)
                                                                   (a$1_0 a$1_0_old)
                                                                   (i.0$1_0 i.0$1_0_old)
                                                                   (n$1_0 n$1_0_old)
                                                                   (_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                                  (=>
                                                                     _$2_6
                                                                     (let
                                                                        ((_$2_10 j.0$2_0_old))
                                                                        (let
                                                                           ((_$2_11 (+ a$2_0_old _$2_10)))
                                                                           (let
                                                                              ((_$2_12 (select HEAP$2_old _$2_11))
                                                                               (_$2_13 i.0$2_0_old))
                                                                              (let
                                                                                 ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                                 (let
                                                                                    ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                                    (let
                                                                                       ((_$2_16 (< _$2_12 _$2_15)))
                                                                                       (=>
                                                                                          (not _$2_16)
                                                                                          (let
                                                                                             ((_$2_27 (+ j.0$2_0_old 1)))
                                                                                             (let
                                                                                                ((j.0$2_0 _$2_27)
                                                                                                 (a$2_0 a$2_0_old)
                                                                                                 (i.0$2_0 i.0$2_0_old)
                                                                                                 (n$2_0 n$2_0_old))
                                                                                                (INV_2_MAIN a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    (not _$1_16)
                                    (let
                                       ((_$1_27 (+ j.0$1_0_old 1)))
                                       (let
                                          ((j.0$1_0 _$1_27)
                                           (a$1_0 a$1_0_old)
                                           (i.0$1_0 i.0$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_6 (< j.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_6
                                             (let
                                                ((_$2_10 j.0$2_0_old))
                                                (let
                                                   ((_$2_11 (+ a$2_0_old _$2_10)))
                                                   (let
                                                      ((_$2_12 (select HEAP$2_old _$2_11))
                                                       (_$2_13 i.0$2_0_old))
                                                      (let
                                                         ((_$2_14 (+ a$2_0_old _$2_13)))
                                                         (let
                                                            ((_$2_15 (select HEAP$2_old _$2_14)))
                                                            (let
                                                               ((_$2_16 (< _$2_12 _$2_15)))
                                                               (=>
                                                                  _$2_16
                                                                  (let
                                                                     ((_$2_17 i.0$2_0_old))
                                                                     (let
                                                                        ((_$2_18 (+ a$2_0_old _$2_17)))
                                                                        (let
                                                                           ((_$2_19 (select HEAP$2_old _$2_18))
                                                                            (_$2_20 j.0$2_0_old))
                                                                           (let
                                                                              ((_$2_21 (+ a$2_0_old _$2_20)))
                                                                              (let
                                                                                 ((_$2_22 (select HEAP$2_old _$2_21))
                                                                                  (_$2_23 i.0$2_0_old))
                                                                                 (let
                                                                                    ((_$2_24 (+ a$2_0_old _$2_23)))
                                                                                    (let
                                                                                       ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                                                        (_$2_25 j.0$2_0_old))
                                                                                       (let
                                                                                          ((_$2_26 (+ a$2_0_old _$2_25)))
                                                                                          (let
                                                                                             ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                                              (_$2_27 (+ j.0$2_0_old 1)))
                                                                                             (let
                                                                                                ((j.0$2_0 _$2_27)
                                                                                                 (a$2_0 a$2_0_old)
                                                                                                 (i.0$2_0 i.0$2_0_old)
                                                                                                 (n$2_0 n$2_0_old))
                                                                                                (INV_2_MAIN a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    (not _$1_16)
                                    (let
                                       ((_$1_27 (+ j.0$1_0_old 1)))
                                       (let
                                          ((j.0$1_0 _$1_27)
                                           (a$1_0 a$1_0_old)
                                           (i.0$1_0 i.0$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_6 (< j.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_6
                                             (let
                                                ((_$2_10 j.0$2_0_old))
                                                (let
                                                   ((_$2_11 (+ a$2_0_old _$2_10)))
                                                   (let
                                                      ((_$2_12 (select HEAP$2_old _$2_11))
                                                       (_$2_13 i.0$2_0_old))
                                                      (let
                                                         ((_$2_14 (+ a$2_0_old _$2_13)))
                                                         (let
                                                            ((_$2_15 (select HEAP$2_old _$2_14)))
                                                            (let
                                                               ((_$2_16 (< _$2_12 _$2_15)))
                                                               (=>
                                                                  (not _$2_16)
                                                                  (let
                                                                     ((_$2_27 (+ j.0$2_0_old 1)))
                                                                     (let
                                                                        ((j.0$2_0 _$2_27)
                                                                         (a$2_0 a$2_0_old)
                                                                         (i.0$2_0 i.0$2_0_old)
                                                                         (n$2_0 n$2_0_old))
                                                                        (INV_2_MAIN a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)))))))))))))))))))))))))
; forbidden main
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1_MAIN a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 0)
                   (_$2_1 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     _$2_1
                     (let
                        ((j.0$2_0 i.0$2_0_old))
                        false))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1_MAIN a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((j.0$1_0 i.0$1_0_old)
                   (_$2_1 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_1)
                     (let
                        ((result$2 0))
                        false))))))))
; offbyn main
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    _$1_16
                                    (let
                                       ((_$1_17 i.0$1_0_old))
                                       (let
                                          ((_$1_18 (+ a$1_0_old _$1_17)))
                                          (let
                                             ((_$1_19 (select HEAP$1_old _$1_18))
                                              (_$1_20 j.0$1_0_old))
                                             (let
                                                ((_$1_21 (+ a$1_0_old _$1_20)))
                                                (let
                                                   ((_$1_22 (select HEAP$1_old _$1_21))
                                                    (_$1_23 i.0$1_0_old))
                                                   (let
                                                      ((_$1_24 (+ a$1_0_old _$1_23)))
                                                      (let
                                                         ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                          (_$1_25 j.0$1_0_old))
                                                         (let
                                                            ((_$1_26 (+ a$1_0_old _$1_25)))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                (_$1_27 (+ j.0$1_0_old 1)))
                                                               (let
                                                                  ((j.0$1_0 _$1_27)
                                                                   (a$1_0 a$1_0_old)
                                                                   (i.0$1_0 i.0$1_0_old)
                                                                   (n$1_0 n$1_0_old))
                                                                  (=>
                                                                     (and
                                                                        (let
                                                                           ((_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                                           (=>
                                                                              _$2_6
                                                                              (let
                                                                                 ((_$2_10 j.0$2_0_old))
                                                                                 (let
                                                                                    ((_$2_11 (+ a$2_0_old _$2_10)))
                                                                                    (let
                                                                                       ((_$2_12 (select HEAP$2_old _$2_11))
                                                                                        (_$2_13 i.0$2_0_old))
                                                                                       (let
                                                                                          ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                                          (let
                                                                                             ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                                             (let
                                                                                                ((_$2_16 (< _$2_12 _$2_15)))
                                                                                                (=>
                                                                                                   _$2_16
                                                                                                   (let
                                                                                                      ((_$2_17 i.0$2_0_old))
                                                                                                      (let
                                                                                                         ((_$2_18 (+ a$2_0_old _$2_17)))
                                                                                                         (let
                                                                                                            ((_$2_19 (select HEAP$2_old _$2_18))
                                                                                                             (_$2_20 j.0$2_0_old))
                                                                                                            (let
                                                                                                               ((_$2_21 (+ a$2_0_old _$2_20)))
                                                                                                               (let
                                                                                                                  ((_$2_22 (select HEAP$2_old _$2_21))
                                                                                                                   (_$2_23 i.0$2_0_old))
                                                                                                                  (let
                                                                                                                     ((_$2_24 (+ a$2_0_old _$2_23)))
                                                                                                                     (let
                                                                                                                        ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                                                                                         (_$2_25 j.0$2_0_old))
                                                                                                                        (let
                                                                                                                           ((_$2_26 (+ a$2_0_old _$2_25)))
                                                                                                                           (let
                                                                                                                              ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                                                                               (_$2_27 (+ j.0$2_0_old 1)))
                                                                                                                              (let
                                                                                                                                 ((j.0$2_0 _$2_27)
                                                                                                                                  (a$2_0 a$2_0_old)
                                                                                                                                  (i.0$2_0 i.0$2_0_old)
                                                                                                                                  (n$2_0 n$2_0_old))
                                                                                                                                 false)))))))))))))))))))
                                                                        (let
                                                                           ((_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                                           (=>
                                                                              _$2_6
                                                                              (let
                                                                                 ((_$2_10 j.0$2_0_old))
                                                                                 (let
                                                                                    ((_$2_11 (+ a$2_0_old _$2_10)))
                                                                                    (let
                                                                                       ((_$2_12 (select HEAP$2_old _$2_11))
                                                                                        (_$2_13 i.0$2_0_old))
                                                                                       (let
                                                                                          ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                                          (let
                                                                                             ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                                             (let
                                                                                                ((_$2_16 (< _$2_12 _$2_15)))
                                                                                                (=>
                                                                                                   (not _$2_16)
                                                                                                   (let
                                                                                                      ((_$2_27 (+ j.0$2_0_old 1)))
                                                                                                      (let
                                                                                                         ((j.0$2_0 _$2_27)
                                                                                                          (a$2_0 a$2_0_old)
                                                                                                          (i.0$2_0 i.0$2_0_old)
                                                                                                          (n$2_0 n$2_0_old))
                                                                                                         false))))))))))))
                                                                     (INV_2_MAIN a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    (not _$1_16)
                                    (let
                                       ((_$1_27 (+ j.0$1_0_old 1)))
                                       (let
                                          ((j.0$1_0 _$1_27)
                                           (a$1_0 a$1_0_old)
                                           (i.0$1_0 i.0$1_0_old)
                                           (n$1_0 n$1_0_old))
                                          (=>
                                             (and
                                                (let
                                                   ((_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_6
                                                      (let
                                                         ((_$2_10 j.0$2_0_old))
                                                         (let
                                                            ((_$2_11 (+ a$2_0_old _$2_10)))
                                                            (let
                                                               ((_$2_12 (select HEAP$2_old _$2_11))
                                                                (_$2_13 i.0$2_0_old))
                                                               (let
                                                                  ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                  (let
                                                                     ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                     (let
                                                                        ((_$2_16 (< _$2_12 _$2_15)))
                                                                        (=>
                                                                           _$2_16
                                                                           (let
                                                                              ((_$2_17 i.0$2_0_old))
                                                                              (let
                                                                                 ((_$2_18 (+ a$2_0_old _$2_17)))
                                                                                 (let
                                                                                    ((_$2_19 (select HEAP$2_old _$2_18))
                                                                                     (_$2_20 j.0$2_0_old))
                                                                                    (let
                                                                                       ((_$2_21 (+ a$2_0_old _$2_20)))
                                                                                       (let
                                                                                          ((_$2_22 (select HEAP$2_old _$2_21))
                                                                                           (_$2_23 i.0$2_0_old))
                                                                                          (let
                                                                                             ((_$2_24 (+ a$2_0_old _$2_23)))
                                                                                             (let
                                                                                                ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                                                                 (_$2_25 j.0$2_0_old))
                                                                                                (let
                                                                                                   ((_$2_26 (+ a$2_0_old _$2_25)))
                                                                                                   (let
                                                                                                      ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                                                       (_$2_27 (+ j.0$2_0_old 1)))
                                                                                                      (let
                                                                                                         ((j.0$2_0 _$2_27)
                                                                                                          (a$2_0 a$2_0_old)
                                                                                                          (i.0$2_0 i.0$2_0_old)
                                                                                                          (n$2_0 n$2_0_old))
                                                                                                         false)))))))))))))))))))
                                                (let
                                                   ((_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_6
                                                      (let
                                                         ((_$2_10 j.0$2_0_old))
                                                         (let
                                                            ((_$2_11 (+ a$2_0_old _$2_10)))
                                                            (let
                                                               ((_$2_12 (select HEAP$2_old _$2_11))
                                                                (_$2_13 i.0$2_0_old))
                                                               (let
                                                                  ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                  (let
                                                                     ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                     (let
                                                                        ((_$2_16 (< _$2_12 _$2_15)))
                                                                        (=>
                                                                           (not _$2_16)
                                                                           (let
                                                                              ((_$2_27 (+ j.0$2_0_old 1)))
                                                                              (let
                                                                                 ((j.0$2_0 _$2_27)
                                                                                  (a$2_0 a$2_0_old)
                                                                                  (i.0$2_0 i.0$2_0_old)
                                                                                  (n$2_0 n$2_0_old))
                                                                                 false))))))))))))
                                             (INV_2_MAIN a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$2_6 (< j.0$2_0_old n$2_0_old)))
            (=>
               _$2_6
               (let
                  ((_$2_10 j.0$2_0_old))
                  (let
                     ((_$2_11 (+ a$2_0_old _$2_10)))
                     (let
                        ((_$2_12 (select HEAP$2_old _$2_11))
                         (_$2_13 i.0$2_0_old))
                        (let
                           ((_$2_14 (+ a$2_0_old _$2_13)))
                           (let
                              ((_$2_15 (select HEAP$2_old _$2_14)))
                              (let
                                 ((_$2_16 (< _$2_12 _$2_15)))
                                 (=>
                                    _$2_16
                                    (let
                                       ((_$2_17 i.0$2_0_old))
                                       (let
                                          ((_$2_18 (+ a$2_0_old _$2_17)))
                                          (let
                                             ((_$2_19 (select HEAP$2_old _$2_18))
                                              (_$2_20 j.0$2_0_old))
                                             (let
                                                ((_$2_21 (+ a$2_0_old _$2_20)))
                                                (let
                                                   ((_$2_22 (select HEAP$2_old _$2_21))
                                                    (_$2_23 i.0$2_0_old))
                                                   (let
                                                      ((_$2_24 (+ a$2_0_old _$2_23)))
                                                      (let
                                                         ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                          (_$2_25 j.0$2_0_old))
                                                         (let
                                                            ((_$2_26 (+ a$2_0_old _$2_25)))
                                                            (let
                                                               ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                (_$2_27 (+ j.0$2_0_old 1)))
                                                               (let
                                                                  ((j.0$2_0 _$2_27)
                                                                   (a$2_0 a$2_0_old)
                                                                   (i.0$2_0 i.0$2_0_old)
                                                                   (n$2_0 n$2_0_old))
                                                                  (=>
                                                                     (and
                                                                        (let
                                                                           ((_$1_6 (< j.0$1_0_old n$1_0_old)))
                                                                           (=>
                                                                              _$1_6
                                                                              (let
                                                                                 ((_$1_10 j.0$1_0_old))
                                                                                 (let
                                                                                    ((_$1_11 (+ a$1_0_old _$1_10)))
                                                                                    (let
                                                                                       ((_$1_12 (select HEAP$1_old _$1_11))
                                                                                        (_$1_13 i.0$1_0_old))
                                                                                       (let
                                                                                          ((_$1_14 (+ a$1_0_old _$1_13)))
                                                                                          (let
                                                                                             ((_$1_15 (select HEAP$1_old _$1_14)))
                                                                                             (let
                                                                                                ((_$1_16 (<= _$1_12 _$1_15)))
                                                                                                (=>
                                                                                                   _$1_16
                                                                                                   (let
                                                                                                      ((_$1_17 i.0$1_0_old))
                                                                                                      (let
                                                                                                         ((_$1_18 (+ a$1_0_old _$1_17)))
                                                                                                         (let
                                                                                                            ((_$1_19 (select HEAP$1_old _$1_18))
                                                                                                             (_$1_20 j.0$1_0_old))
                                                                                                            (let
                                                                                                               ((_$1_21 (+ a$1_0_old _$1_20)))
                                                                                                               (let
                                                                                                                  ((_$1_22 (select HEAP$1_old _$1_21))
                                                                                                                   (_$1_23 i.0$1_0_old))
                                                                                                                  (let
                                                                                                                     ((_$1_24 (+ a$1_0_old _$1_23)))
                                                                                                                     (let
                                                                                                                        ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                                                                                         (_$1_25 j.0$1_0_old))
                                                                                                                        (let
                                                                                                                           ((_$1_26 (+ a$1_0_old _$1_25)))
                                                                                                                           (let
                                                                                                                              ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                                                                               (_$1_27 (+ j.0$1_0_old 1)))
                                                                                                                              (let
                                                                                                                                 ((j.0$1_0 _$1_27)
                                                                                                                                  (a$1_0 a$1_0_old)
                                                                                                                                  (i.0$1_0 i.0$1_0_old)
                                                                                                                                  (n$1_0 n$1_0_old))
                                                                                                                                 false)))))))))))))))))))
                                                                        (let
                                                                           ((_$1_6 (< j.0$1_0_old n$1_0_old)))
                                                                           (=>
                                                                              _$1_6
                                                                              (let
                                                                                 ((_$1_10 j.0$1_0_old))
                                                                                 (let
                                                                                    ((_$1_11 (+ a$1_0_old _$1_10)))
                                                                                    (let
                                                                                       ((_$1_12 (select HEAP$1_old _$1_11))
                                                                                        (_$1_13 i.0$1_0_old))
                                                                                       (let
                                                                                          ((_$1_14 (+ a$1_0_old _$1_13)))
                                                                                          (let
                                                                                             ((_$1_15 (select HEAP$1_old _$1_14)))
                                                                                             (let
                                                                                                ((_$1_16 (<= _$1_12 _$1_15)))
                                                                                                (=>
                                                                                                   (not _$1_16)
                                                                                                   (let
                                                                                                      ((_$1_27 (+ j.0$1_0_old 1)))
                                                                                                      (let
                                                                                                         ((j.0$1_0 _$1_27)
                                                                                                          (a$1_0 a$1_0_old)
                                                                                                          (i.0$1_0 i.0$1_0_old)
                                                                                                          (n$1_0 n$1_0_old))
                                                                                                         false))))))))))))
                                                                     (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0 i.0$2_0 j.0$2_0 n$2_0))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$2_6 (< j.0$2_0_old n$2_0_old)))
            (=>
               _$2_6
               (let
                  ((_$2_10 j.0$2_0_old))
                  (let
                     ((_$2_11 (+ a$2_0_old _$2_10)))
                     (let
                        ((_$2_12 (select HEAP$2_old _$2_11))
                         (_$2_13 i.0$2_0_old))
                        (let
                           ((_$2_14 (+ a$2_0_old _$2_13)))
                           (let
                              ((_$2_15 (select HEAP$2_old _$2_14)))
                              (let
                                 ((_$2_16 (< _$2_12 _$2_15)))
                                 (=>
                                    (not _$2_16)
                                    (let
                                       ((_$2_27 (+ j.0$2_0_old 1)))
                                       (let
                                          ((j.0$2_0 _$2_27)
                                           (a$2_0 a$2_0_old)
                                           (i.0$2_0 i.0$2_0_old)
                                           (n$2_0 n$2_0_old))
                                          (=>
                                             (and
                                                (let
                                                   ((_$1_6 (< j.0$1_0_old n$1_0_old)))
                                                   (=>
                                                      _$1_6
                                                      (let
                                                         ((_$1_10 j.0$1_0_old))
                                                         (let
                                                            ((_$1_11 (+ a$1_0_old _$1_10)))
                                                            (let
                                                               ((_$1_12 (select HEAP$1_old _$1_11))
                                                                (_$1_13 i.0$1_0_old))
                                                               (let
                                                                  ((_$1_14 (+ a$1_0_old _$1_13)))
                                                                  (let
                                                                     ((_$1_15 (select HEAP$1_old _$1_14)))
                                                                     (let
                                                                        ((_$1_16 (<= _$1_12 _$1_15)))
                                                                        (=>
                                                                           _$1_16
                                                                           (let
                                                                              ((_$1_17 i.0$1_0_old))
                                                                              (let
                                                                                 ((_$1_18 (+ a$1_0_old _$1_17)))
                                                                                 (let
                                                                                    ((_$1_19 (select HEAP$1_old _$1_18))
                                                                                     (_$1_20 j.0$1_0_old))
                                                                                    (let
                                                                                       ((_$1_21 (+ a$1_0_old _$1_20)))
                                                                                       (let
                                                                                          ((_$1_22 (select HEAP$1_old _$1_21))
                                                                                           (_$1_23 i.0$1_0_old))
                                                                                          (let
                                                                                             ((_$1_24 (+ a$1_0_old _$1_23)))
                                                                                             (let
                                                                                                ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                                                                 (_$1_25 j.0$1_0_old))
                                                                                                (let
                                                                                                   ((_$1_26 (+ a$1_0_old _$1_25)))
                                                                                                   (let
                                                                                                      ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                                                       (_$1_27 (+ j.0$1_0_old 1)))
                                                                                                      (let
                                                                                                         ((j.0$1_0 _$1_27)
                                                                                                          (a$1_0 a$1_0_old)
                                                                                                          (i.0$1_0 i.0$1_0_old)
                                                                                                          (n$1_0 n$1_0_old))
                                                                                                         false)))))))))))))))))))
                                                (let
                                                   ((_$1_6 (< j.0$1_0_old n$1_0_old)))
                                                   (=>
                                                      _$1_6
                                                      (let
                                                         ((_$1_10 j.0$1_0_old))
                                                         (let
                                                            ((_$1_11 (+ a$1_0_old _$1_10)))
                                                            (let
                                                               ((_$1_12 (select HEAP$1_old _$1_11))
                                                                (_$1_13 i.0$1_0_old))
                                                               (let
                                                                  ((_$1_14 (+ a$1_0_old _$1_13)))
                                                                  (let
                                                                     ((_$1_15 (select HEAP$1_old _$1_14)))
                                                                     (let
                                                                        ((_$1_16 (<= _$1_12 _$1_15)))
                                                                        (=>
                                                                           (not _$1_16)
                                                                           (let
                                                                              ((_$1_27 (+ j.0$1_0_old 1)))
                                                                              (let
                                                                                 ((j.0$1_0 _$1_27)
                                                                                  (a$1_0 a$1_0_old)
                                                                                  (i.0$1_0 i.0$1_0_old)
                                                                                  (n$1_0 n$1_0_old))
                                                                                 false))))))))))))
                                             (INV_2_MAIN a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0 i.0$2_0 j.0$2_0 n$2_0))))))))))))))))
; end
(assert
   (forall
      ((a$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_selsort_PRE a$1_0_old n$1_0_old a$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 0)
             (a$1_0 a$1_0_old)
             (n$1_0 n$1_0_old)
             (i.0$2_0 0)
             (a$2_0 a$2_0_old)
             (n$2_0 n$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_1_PRE a$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0)
                  (=>
                     (INV_1 a$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0 result$1 result$2)
                     (INV_REC_selsort a$1_0_old n$1_0_old a$2_0_old n$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1_PRE a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 0)
                   (_$2_1 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_1)
                     (let
                        ((result$2 0))
                        (INV_1 a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old result$1 result$2)))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1_PRE a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((j.0$1_0 i.0$1_0_old)
                   (a$1_0 a$1_0_old)
                   (i.0$1_0 i.0$1_0_old)
                   (n$1_0 n$1_0_old)
                   (_$2_1 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     _$2_1
                     (let
                        ((j.0$2_0 i.0$2_0_old)
                         (a$2_0 a$2_0_old)
                         (i.0$2_0 i.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_2_PRE a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)
                              (=>
                                 (INV_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$1 result$2)
                                 (INV_1 a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_6)
               (let
                  ((_$1_28 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_28)
                      (a$1_0 a$1_0_old)
                      (n$1_0 n$1_0_old)
                      (_$2_6 (< j.0$2_0_old n$2_0_old)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_28 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_28)
                               (a$2_0 a$2_0_old)
                               (n$2_0 n$2_0_old))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_1_PRE a$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0)
                                    (=>
                                       (INV_1 a$1_0 i.0$1_0 n$1_0 a$2_0 i.0$2_0 n$2_0 result$1 result$2)
                                       (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    _$1_16
                                    (let
                                       ((_$1_17 i.0$1_0_old))
                                       (let
                                          ((_$1_18 (+ a$1_0_old _$1_17)))
                                          (let
                                             ((_$1_19 (select HEAP$1_old _$1_18))
                                              (_$1_20 j.0$1_0_old))
                                             (let
                                                ((_$1_21 (+ a$1_0_old _$1_20)))
                                                (let
                                                   ((_$1_22 (select HEAP$1_old _$1_21))
                                                    (_$1_23 i.0$1_0_old))
                                                   (let
                                                      ((_$1_24 (+ a$1_0_old _$1_23)))
                                                      (let
                                                         ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                          (_$1_25 j.0$1_0_old))
                                                         (let
                                                            ((_$1_26 (+ a$1_0_old _$1_25)))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                (_$1_27 (+ j.0$1_0_old 1)))
                                                               (let
                                                                  ((j.0$1_0 _$1_27)
                                                                   (a$1_0 a$1_0_old)
                                                                   (i.0$1_0 i.0$1_0_old)
                                                                   (n$1_0 n$1_0_old)
                                                                   (_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                                  (=>
                                                                     _$2_6
                                                                     (let
                                                                        ((_$2_10 j.0$2_0_old))
                                                                        (let
                                                                           ((_$2_11 (+ a$2_0_old _$2_10)))
                                                                           (let
                                                                              ((_$2_12 (select HEAP$2_old _$2_11))
                                                                               (_$2_13 i.0$2_0_old))
                                                                              (let
                                                                                 ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                                 (let
                                                                                    ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                                    (let
                                                                                       ((_$2_16 (< _$2_12 _$2_15)))
                                                                                       (=>
                                                                                          _$2_16
                                                                                          (let
                                                                                             ((_$2_17 i.0$2_0_old))
                                                                                             (let
                                                                                                ((_$2_18 (+ a$2_0_old _$2_17)))
                                                                                                (let
                                                                                                   ((_$2_19 (select HEAP$2_old _$2_18))
                                                                                                    (_$2_20 j.0$2_0_old))
                                                                                                   (let
                                                                                                      ((_$2_21 (+ a$2_0_old _$2_20)))
                                                                                                      (let
                                                                                                         ((_$2_22 (select HEAP$2_old _$2_21))
                                                                                                          (_$2_23 i.0$2_0_old))
                                                                                                         (let
                                                                                                            ((_$2_24 (+ a$2_0_old _$2_23)))
                                                                                                            (let
                                                                                                               ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                                                                                (_$2_25 j.0$2_0_old))
                                                                                                               (let
                                                                                                                  ((_$2_26 (+ a$2_0_old _$2_25)))
                                                                                                                  (let
                                                                                                                     ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                                                                      (_$2_27 (+ j.0$2_0_old 1)))
                                                                                                                     (let
                                                                                                                        ((j.0$2_0 _$2_27)
                                                                                                                         (a$2_0 a$2_0_old)
                                                                                                                         (i.0$2_0 i.0$2_0_old)
                                                                                                                         (n$2_0 n$2_0_old))
                                                                                                                        (forall
                                                                                                                           ((result$1 Int)
                                                                                                                            (result$2 Int))
                                                                                                                           (and
                                                                                                                              (INV_2_PRE a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)
                                                                                                                              (=>
                                                                                                                                 (INV_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$1 result$2)
                                                                                                                                 (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    _$1_16
                                    (let
                                       ((_$1_17 i.0$1_0_old))
                                       (let
                                          ((_$1_18 (+ a$1_0_old _$1_17)))
                                          (let
                                             ((_$1_19 (select HEAP$1_old _$1_18))
                                              (_$1_20 j.0$1_0_old))
                                             (let
                                                ((_$1_21 (+ a$1_0_old _$1_20)))
                                                (let
                                                   ((_$1_22 (select HEAP$1_old _$1_21))
                                                    (_$1_23 i.0$1_0_old))
                                                   (let
                                                      ((_$1_24 (+ a$1_0_old _$1_23)))
                                                      (let
                                                         ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                          (_$1_25 j.0$1_0_old))
                                                         (let
                                                            ((_$1_26 (+ a$1_0_old _$1_25)))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                (_$1_27 (+ j.0$1_0_old 1)))
                                                               (let
                                                                  ((j.0$1_0 _$1_27)
                                                                   (a$1_0 a$1_0_old)
                                                                   (i.0$1_0 i.0$1_0_old)
                                                                   (n$1_0 n$1_0_old)
                                                                   (_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                                  (=>
                                                                     _$2_6
                                                                     (let
                                                                        ((_$2_10 j.0$2_0_old))
                                                                        (let
                                                                           ((_$2_11 (+ a$2_0_old _$2_10)))
                                                                           (let
                                                                              ((_$2_12 (select HEAP$2_old _$2_11))
                                                                               (_$2_13 i.0$2_0_old))
                                                                              (let
                                                                                 ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                                 (let
                                                                                    ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                                    (let
                                                                                       ((_$2_16 (< _$2_12 _$2_15)))
                                                                                       (=>
                                                                                          (not _$2_16)
                                                                                          (let
                                                                                             ((_$2_27 (+ j.0$2_0_old 1)))
                                                                                             (let
                                                                                                ((j.0$2_0 _$2_27)
                                                                                                 (a$2_0 a$2_0_old)
                                                                                                 (i.0$2_0 i.0$2_0_old)
                                                                                                 (n$2_0 n$2_0_old))
                                                                                                (forall
                                                                                                   ((result$1 Int)
                                                                                                    (result$2 Int))
                                                                                                   (and
                                                                                                      (INV_2_PRE a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)
                                                                                                      (=>
                                                                                                         (INV_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$1 result$2)
                                                                                                         (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    (not _$1_16)
                                    (let
                                       ((_$1_27 (+ j.0$1_0_old 1)))
                                       (let
                                          ((j.0$1_0 _$1_27)
                                           (a$1_0 a$1_0_old)
                                           (i.0$1_0 i.0$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_6 (< j.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_6
                                             (let
                                                ((_$2_10 j.0$2_0_old))
                                                (let
                                                   ((_$2_11 (+ a$2_0_old _$2_10)))
                                                   (let
                                                      ((_$2_12 (select HEAP$2_old _$2_11))
                                                       (_$2_13 i.0$2_0_old))
                                                      (let
                                                         ((_$2_14 (+ a$2_0_old _$2_13)))
                                                         (let
                                                            ((_$2_15 (select HEAP$2_old _$2_14)))
                                                            (let
                                                               ((_$2_16 (< _$2_12 _$2_15)))
                                                               (=>
                                                                  _$2_16
                                                                  (let
                                                                     ((_$2_17 i.0$2_0_old))
                                                                     (let
                                                                        ((_$2_18 (+ a$2_0_old _$2_17)))
                                                                        (let
                                                                           ((_$2_19 (select HEAP$2_old _$2_18))
                                                                            (_$2_20 j.0$2_0_old))
                                                                           (let
                                                                              ((_$2_21 (+ a$2_0_old _$2_20)))
                                                                              (let
                                                                                 ((_$2_22 (select HEAP$2_old _$2_21))
                                                                                  (_$2_23 i.0$2_0_old))
                                                                                 (let
                                                                                    ((_$2_24 (+ a$2_0_old _$2_23)))
                                                                                    (let
                                                                                       ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                                                        (_$2_25 j.0$2_0_old))
                                                                                       (let
                                                                                          ((_$2_26 (+ a$2_0_old _$2_25)))
                                                                                          (let
                                                                                             ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                                              (_$2_27 (+ j.0$2_0_old 1)))
                                                                                             (let
                                                                                                ((j.0$2_0 _$2_27)
                                                                                                 (a$2_0 a$2_0_old)
                                                                                                 (i.0$2_0 i.0$2_0_old)
                                                                                                 (n$2_0 n$2_0_old))
                                                                                                (forall
                                                                                                   ((result$1 Int)
                                                                                                    (result$2 Int))
                                                                                                   (and
                                                                                                      (INV_2_PRE a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)
                                                                                                      (=>
                                                                                                         (INV_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$1 result$2)
                                                                                                         (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    (not _$1_16)
                                    (let
                                       ((_$1_27 (+ j.0$1_0_old 1)))
                                       (let
                                          ((j.0$1_0 _$1_27)
                                           (a$1_0 a$1_0_old)
                                           (i.0$1_0 i.0$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_6 (< j.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_6
                                             (let
                                                ((_$2_10 j.0$2_0_old))
                                                (let
                                                   ((_$2_11 (+ a$2_0_old _$2_10)))
                                                   (let
                                                      ((_$2_12 (select HEAP$2_old _$2_11))
                                                       (_$2_13 i.0$2_0_old))
                                                      (let
                                                         ((_$2_14 (+ a$2_0_old _$2_13)))
                                                         (let
                                                            ((_$2_15 (select HEAP$2_old _$2_14)))
                                                            (let
                                                               ((_$2_16 (< _$2_12 _$2_15)))
                                                               (=>
                                                                  (not _$2_16)
                                                                  (let
                                                                     ((_$2_27 (+ j.0$2_0_old 1)))
                                                                     (let
                                                                        ((j.0$2_0 _$2_27)
                                                                         (a$2_0 a$2_0_old)
                                                                         (i.0$2_0 i.0$2_0_old)
                                                                         (n$2_0 n$2_0_old))
                                                                        (forall
                                                                           ((result$1 Int)
                                                                            (result$2 Int))
                                                                           (and
                                                                              (INV_2_PRE a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0)
                                                                              (=>
                                                                                 (INV_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$1 result$2)
                                                                                 (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_selsort__1_PRE a$1_0_old n$1_0_old)
         (let
            ((i.0$1_0 0)
             (a$1_0 a$1_0_old)
             (n$1_0 n$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_1__1 a$1_0 i.0$1_0 n$1_0 result$1)
                  (INV_REC_selsort__1 a$1_0_old n$1_0_old result$1)))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_1__1_PRE a$1_0_old i.0$1_0_old n$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 0))
                  (INV_1__1 a$1_0_old i.0$1_0_old n$1_0_old result$1)))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_1__1_PRE a$1_0_old i.0$1_0_old n$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((j.0$1_0 i.0$1_0_old)
                   (a$1_0 a$1_0_old)
                   (i.0$1_0 i.0$1_0_old)
                   (n$1_0 n$1_0_old))
                  (forall
                     ((result$1 Int))
                     (=>
                        (INV_2__1 a$1_0 i.0$1_0 j.0$1_0 n$1_0 result$1)
                        (INV_1__1 a$1_0_old i.0$1_0_old n$1_0_old result$1)))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_2__1_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_6)
               (let
                  ((_$1_28 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_28)
                      (a$1_0 a$1_0_old)
                      (n$1_0 n$1_0_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_1__1 a$1_0 i.0$1_0 n$1_0 result$1)
                           (INV_2__1 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old result$1))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_2__1_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    _$1_16
                                    (let
                                       ((_$1_17 i.0$1_0_old))
                                       (let
                                          ((_$1_18 (+ a$1_0_old _$1_17)))
                                          (let
                                             ((_$1_19 (select HEAP$1_old _$1_18))
                                              (_$1_20 j.0$1_0_old))
                                             (let
                                                ((_$1_21 (+ a$1_0_old _$1_20)))
                                                (let
                                                   ((_$1_22 (select HEAP$1_old _$1_21))
                                                    (_$1_23 i.0$1_0_old))
                                                   (let
                                                      ((_$1_24 (+ a$1_0_old _$1_23)))
                                                      (let
                                                         ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                          (_$1_25 j.0$1_0_old))
                                                         (let
                                                            ((_$1_26 (+ a$1_0_old _$1_25)))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                (_$1_27 (+ j.0$1_0_old 1)))
                                                               (let
                                                                  ((j.0$1_0 _$1_27)
                                                                   (a$1_0 a$1_0_old)
                                                                   (i.0$1_0 i.0$1_0_old)
                                                                   (n$1_0 n$1_0_old))
                                                                  (forall
                                                                     ((result$1 Int))
                                                                     (=>
                                                                        (INV_2__1 a$1_0 i.0$1_0 j.0$1_0 n$1_0 result$1)
                                                                        (INV_2__1 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old result$1)))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_2__1_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    (not _$1_16)
                                    (let
                                       ((_$1_27 (+ j.0$1_0_old 1)))
                                       (let
                                          ((j.0$1_0 _$1_27)
                                           (a$1_0 a$1_0_old)
                                           (i.0$1_0 i.0$1_0_old)
                                           (n$1_0 n$1_0_old))
                                          (forall
                                             ((result$1 Int))
                                             (=>
                                                (INV_2__1 a$1_0 i.0$1_0 j.0$1_0 n$1_0 result$1)
                                                (INV_2__1 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old result$1)))))))))))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_selsort__2_PRE a$2_0_old n$2_0_old)
         (let
            ((i.0$2_0 0)
             (a$2_0 a$2_0_old)
             (n$2_0 n$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_1__2 a$2_0 i.0$2_0 n$2_0 result$2)
                  (INV_REC_selsort__2 a$2_0_old n$2_0_old result$2)))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1__2_PRE a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$2_1 (< i.0$2_0_old n$2_0_old)))
            (=>
               (not _$2_1)
               (let
                  ((result$2 0))
                  (INV_1__2 a$2_0_old i.0$2_0_old n$2_0_old result$2)))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1__2_PRE a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$2_1 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_1
               (let
                  ((j.0$2_0 i.0$2_0_old)
                   (a$2_0 a$2_0_old)
                   (i.0$2_0 i.0$2_0_old)
                   (n$2_0 n$2_0_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_2__2 a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$2)
                        (INV_1__2 a$2_0_old i.0$2_0_old n$2_0_old result$2)))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2__2_PRE a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$2_6 (< j.0$2_0_old n$2_0_old)))
            (=>
               (not _$2_6)
               (let
                  ((_$2_28 (+ i.0$2_0_old 1)))
                  (let
                     ((i.0$2_0 _$2_28)
                      (a$2_0 a$2_0_old)
                      (n$2_0 n$2_0_old))
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_1__2 a$2_0 i.0$2_0 n$2_0 result$2)
                           (INV_2__2 a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$2))))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2__2_PRE a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$2_6 (< j.0$2_0_old n$2_0_old)))
            (=>
               _$2_6
               (let
                  ((_$2_10 j.0$2_0_old))
                  (let
                     ((_$2_11 (+ a$2_0_old _$2_10)))
                     (let
                        ((_$2_12 (select HEAP$2_old _$2_11))
                         (_$2_13 i.0$2_0_old))
                        (let
                           ((_$2_14 (+ a$2_0_old _$2_13)))
                           (let
                              ((_$2_15 (select HEAP$2_old _$2_14)))
                              (let
                                 ((_$2_16 (< _$2_12 _$2_15)))
                                 (=>
                                    _$2_16
                                    (let
                                       ((_$2_17 i.0$2_0_old))
                                       (let
                                          ((_$2_18 (+ a$2_0_old _$2_17)))
                                          (let
                                             ((_$2_19 (select HEAP$2_old _$2_18))
                                              (_$2_20 j.0$2_0_old))
                                             (let
                                                ((_$2_21 (+ a$2_0_old _$2_20)))
                                                (let
                                                   ((_$2_22 (select HEAP$2_old _$2_21))
                                                    (_$2_23 i.0$2_0_old))
                                                   (let
                                                      ((_$2_24 (+ a$2_0_old _$2_23)))
                                                      (let
                                                         ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                          (_$2_25 j.0$2_0_old))
                                                         (let
                                                            ((_$2_26 (+ a$2_0_old _$2_25)))
                                                            (let
                                                               ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                (_$2_27 (+ j.0$2_0_old 1)))
                                                               (let
                                                                  ((j.0$2_0 _$2_27)
                                                                   (a$2_0 a$2_0_old)
                                                                   (i.0$2_0 i.0$2_0_old)
                                                                   (n$2_0 n$2_0_old))
                                                                  (forall
                                                                     ((result$2 Int))
                                                                     (=>
                                                                        (INV_2__2 a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$2)
                                                                        (INV_2__2 a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$2)))))))))))))))))))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2__2_PRE a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$2_6 (< j.0$2_0_old n$2_0_old)))
            (=>
               _$2_6
               (let
                  ((_$2_10 j.0$2_0_old))
                  (let
                     ((_$2_11 (+ a$2_0_old _$2_10)))
                     (let
                        ((_$2_12 (select HEAP$2_old _$2_11))
                         (_$2_13 i.0$2_0_old))
                        (let
                           ((_$2_14 (+ a$2_0_old _$2_13)))
                           (let
                              ((_$2_15 (select HEAP$2_old _$2_14)))
                              (let
                                 ((_$2_16 (< _$2_12 _$2_15)))
                                 (=>
                                    (not _$2_16)
                                    (let
                                       ((_$2_27 (+ j.0$2_0_old 1)))
                                       (let
                                          ((j.0$2_0 _$2_27)
                                           (a$2_0 a$2_0_old)
                                           (i.0$2_0 i.0$2_0_old)
                                           (n$2_0 n$2_0_old))
                                          (forall
                                             ((result$2 Int))
                                             (=>
                                                (INV_2__2 a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$2)
                                                (INV_2__2 a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$2)))))))))))))))))
; FORBIDDEN PATHS
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1_PRE a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 0)
                   (_$2_1 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     _$2_1
                     (let
                        ((j.0$2_0 i.0$2_0_old))
                        false))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_1_PRE a$1_0_old i.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((j.0$1_0 i.0$1_0_old)
                   (_$2_1 (< i.0$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_1)
                     (let
                        ((result$2 0))
                        false))))))))
; OFF BY N
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    _$1_16
                                    (let
                                       ((_$1_17 i.0$1_0_old))
                                       (let
                                          ((_$1_18 (+ a$1_0_old _$1_17)))
                                          (let
                                             ((_$1_19 (select HEAP$1_old _$1_18))
                                              (_$1_20 j.0$1_0_old))
                                             (let
                                                ((_$1_21 (+ a$1_0_old _$1_20)))
                                                (let
                                                   ((_$1_22 (select HEAP$1_old _$1_21))
                                                    (_$1_23 i.0$1_0_old))
                                                   (let
                                                      ((_$1_24 (+ a$1_0_old _$1_23)))
                                                      (let
                                                         ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                          (_$1_25 j.0$1_0_old))
                                                         (let
                                                            ((_$1_26 (+ a$1_0_old _$1_25)))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                (_$1_27 (+ j.0$1_0_old 1)))
                                                               (let
                                                                  ((j.0$1_0 _$1_27)
                                                                   (a$1_0 a$1_0_old)
                                                                   (i.0$1_0 i.0$1_0_old)
                                                                   (n$1_0 n$1_0_old))
                                                                  (=>
                                                                     (and
                                                                        (let
                                                                           ((_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                                           (=>
                                                                              _$2_6
                                                                              (let
                                                                                 ((_$2_10 j.0$2_0_old))
                                                                                 (let
                                                                                    ((_$2_11 (+ a$2_0_old _$2_10)))
                                                                                    (let
                                                                                       ((_$2_12 (select HEAP$2_old _$2_11))
                                                                                        (_$2_13 i.0$2_0_old))
                                                                                       (let
                                                                                          ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                                          (let
                                                                                             ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                                             (let
                                                                                                ((_$2_16 (< _$2_12 _$2_15)))
                                                                                                (=>
                                                                                                   _$2_16
                                                                                                   (let
                                                                                                      ((_$2_17 i.0$2_0_old))
                                                                                                      (let
                                                                                                         ((_$2_18 (+ a$2_0_old _$2_17)))
                                                                                                         (let
                                                                                                            ((_$2_19 (select HEAP$2_old _$2_18))
                                                                                                             (_$2_20 j.0$2_0_old))
                                                                                                            (let
                                                                                                               ((_$2_21 (+ a$2_0_old _$2_20)))
                                                                                                               (let
                                                                                                                  ((_$2_22 (select HEAP$2_old _$2_21))
                                                                                                                   (_$2_23 i.0$2_0_old))
                                                                                                                  (let
                                                                                                                     ((_$2_24 (+ a$2_0_old _$2_23)))
                                                                                                                     (let
                                                                                                                        ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                                                                                         (_$2_25 j.0$2_0_old))
                                                                                                                        (let
                                                                                                                           ((_$2_26 (+ a$2_0_old _$2_25)))
                                                                                                                           (let
                                                                                                                              ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                                                                               (_$2_27 (+ j.0$2_0_old 1)))
                                                                                                                              (let
                                                                                                                                 ((j.0$2_0 _$2_27)
                                                                                                                                  (a$2_0 a$2_0_old)
                                                                                                                                  (i.0$2_0 i.0$2_0_old)
                                                                                                                                  (n$2_0 n$2_0_old))
                                                                                                                                 false)))))))))))))))))))
                                                                        (let
                                                                           ((_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                                           (=>
                                                                              _$2_6
                                                                              (let
                                                                                 ((_$2_10 j.0$2_0_old))
                                                                                 (let
                                                                                    ((_$2_11 (+ a$2_0_old _$2_10)))
                                                                                    (let
                                                                                       ((_$2_12 (select HEAP$2_old _$2_11))
                                                                                        (_$2_13 i.0$2_0_old))
                                                                                       (let
                                                                                          ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                                          (let
                                                                                             ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                                             (let
                                                                                                ((_$2_16 (< _$2_12 _$2_15)))
                                                                                                (=>
                                                                                                   (not _$2_16)
                                                                                                   (let
                                                                                                      ((_$2_27 (+ j.0$2_0_old 1)))
                                                                                                      (let
                                                                                                         ((j.0$2_0 _$2_27)
                                                                                                          (a$2_0 a$2_0_old)
                                                                                                          (i.0$2_0 i.0$2_0_old)
                                                                                                          (n$2_0 n$2_0_old))
                                                                                                         false))))))))))))
                                                                     (forall
                                                                        ((result$1 Int)
                                                                         (result$2 Int))
                                                                        (and
                                                                           (INV_2_PRE a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
                                                                           (=>
                                                                              (INV_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2)
                                                                              (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$1_6 (< j.0$1_0_old n$1_0_old)))
            (=>
               _$1_6
               (let
                  ((_$1_10 j.0$1_0_old))
                  (let
                     ((_$1_11 (+ a$1_0_old _$1_10)))
                     (let
                        ((_$1_12 (select HEAP$1_old _$1_11))
                         (_$1_13 i.0$1_0_old))
                        (let
                           ((_$1_14 (+ a$1_0_old _$1_13)))
                           (let
                              ((_$1_15 (select HEAP$1_old _$1_14)))
                              (let
                                 ((_$1_16 (<= _$1_12 _$1_15)))
                                 (=>
                                    (not _$1_16)
                                    (let
                                       ((_$1_27 (+ j.0$1_0_old 1)))
                                       (let
                                          ((j.0$1_0 _$1_27)
                                           (a$1_0 a$1_0_old)
                                           (i.0$1_0 i.0$1_0_old)
                                           (n$1_0 n$1_0_old))
                                          (=>
                                             (and
                                                (let
                                                   ((_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_6
                                                      (let
                                                         ((_$2_10 j.0$2_0_old))
                                                         (let
                                                            ((_$2_11 (+ a$2_0_old _$2_10)))
                                                            (let
                                                               ((_$2_12 (select HEAP$2_old _$2_11))
                                                                (_$2_13 i.0$2_0_old))
                                                               (let
                                                                  ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                  (let
                                                                     ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                     (let
                                                                        ((_$2_16 (< _$2_12 _$2_15)))
                                                                        (=>
                                                                           _$2_16
                                                                           (let
                                                                              ((_$2_17 i.0$2_0_old))
                                                                              (let
                                                                                 ((_$2_18 (+ a$2_0_old _$2_17)))
                                                                                 (let
                                                                                    ((_$2_19 (select HEAP$2_old _$2_18))
                                                                                     (_$2_20 j.0$2_0_old))
                                                                                    (let
                                                                                       ((_$2_21 (+ a$2_0_old _$2_20)))
                                                                                       (let
                                                                                          ((_$2_22 (select HEAP$2_old _$2_21))
                                                                                           (_$2_23 i.0$2_0_old))
                                                                                          (let
                                                                                             ((_$2_24 (+ a$2_0_old _$2_23)))
                                                                                             (let
                                                                                                ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                                                                 (_$2_25 j.0$2_0_old))
                                                                                                (let
                                                                                                   ((_$2_26 (+ a$2_0_old _$2_25)))
                                                                                                   (let
                                                                                                      ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                                                       (_$2_27 (+ j.0$2_0_old 1)))
                                                                                                      (let
                                                                                                         ((j.0$2_0 _$2_27)
                                                                                                          (a$2_0 a$2_0_old)
                                                                                                          (i.0$2_0 i.0$2_0_old)
                                                                                                          (n$2_0 n$2_0_old))
                                                                                                         false)))))))))))))))))))
                                                (let
                                                   ((_$2_6 (< j.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_6
                                                      (let
                                                         ((_$2_10 j.0$2_0_old))
                                                         (let
                                                            ((_$2_11 (+ a$2_0_old _$2_10)))
                                                            (let
                                                               ((_$2_12 (select HEAP$2_old _$2_11))
                                                                (_$2_13 i.0$2_0_old))
                                                               (let
                                                                  ((_$2_14 (+ a$2_0_old _$2_13)))
                                                                  (let
                                                                     ((_$2_15 (select HEAP$2_old _$2_14)))
                                                                     (let
                                                                        ((_$2_16 (< _$2_12 _$2_15)))
                                                                        (=>
                                                                           (not _$2_16)
                                                                           (let
                                                                              ((_$2_27 (+ j.0$2_0_old 1)))
                                                                              (let
                                                                                 ((j.0$2_0 _$2_27)
                                                                                  (a$2_0 a$2_0_old)
                                                                                  (i.0$2_0 i.0$2_0_old)
                                                                                  (n$2_0 n$2_0_old))
                                                                                 false))))))))))))
                                             (forall
                                                ((result$1 Int)
                                                 (result$2 Int))
                                                (and
                                                   (INV_2_PRE a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
                                                   (=>
                                                      (INV_2 a$1_0 i.0$1_0 j.0$1_0 n$1_0 a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2)
                                                      (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$2_6 (< j.0$2_0_old n$2_0_old)))
            (=>
               _$2_6
               (let
                  ((_$2_10 j.0$2_0_old))
                  (let
                     ((_$2_11 (+ a$2_0_old _$2_10)))
                     (let
                        ((_$2_12 (select HEAP$2_old _$2_11))
                         (_$2_13 i.0$2_0_old))
                        (let
                           ((_$2_14 (+ a$2_0_old _$2_13)))
                           (let
                              ((_$2_15 (select HEAP$2_old _$2_14)))
                              (let
                                 ((_$2_16 (< _$2_12 _$2_15)))
                                 (=>
                                    _$2_16
                                    (let
                                       ((_$2_17 i.0$2_0_old))
                                       (let
                                          ((_$2_18 (+ a$2_0_old _$2_17)))
                                          (let
                                             ((_$2_19 (select HEAP$2_old _$2_18))
                                              (_$2_20 j.0$2_0_old))
                                             (let
                                                ((_$2_21 (+ a$2_0_old _$2_20)))
                                                (let
                                                   ((_$2_22 (select HEAP$2_old _$2_21))
                                                    (_$2_23 i.0$2_0_old))
                                                   (let
                                                      ((_$2_24 (+ a$2_0_old _$2_23)))
                                                      (let
                                                         ((HEAP$2 (store HEAP$2_old _$2_24 _$2_22))
                                                          (_$2_25 j.0$2_0_old))
                                                         (let
                                                            ((_$2_26 (+ a$2_0_old _$2_25)))
                                                            (let
                                                               ((HEAP$2 (store HEAP$2 _$2_26 _$2_19))
                                                                (_$2_27 (+ j.0$2_0_old 1)))
                                                               (let
                                                                  ((j.0$2_0 _$2_27)
                                                                   (a$2_0 a$2_0_old)
                                                                   (i.0$2_0 i.0$2_0_old)
                                                                   (n$2_0 n$2_0_old))
                                                                  (=>
                                                                     (and
                                                                        (let
                                                                           ((_$1_6 (< j.0$1_0_old n$1_0_old)))
                                                                           (=>
                                                                              _$1_6
                                                                              (let
                                                                                 ((_$1_10 j.0$1_0_old))
                                                                                 (let
                                                                                    ((_$1_11 (+ a$1_0_old _$1_10)))
                                                                                    (let
                                                                                       ((_$1_12 (select HEAP$1_old _$1_11))
                                                                                        (_$1_13 i.0$1_0_old))
                                                                                       (let
                                                                                          ((_$1_14 (+ a$1_0_old _$1_13)))
                                                                                          (let
                                                                                             ((_$1_15 (select HEAP$1_old _$1_14)))
                                                                                             (let
                                                                                                ((_$1_16 (<= _$1_12 _$1_15)))
                                                                                                (=>
                                                                                                   _$1_16
                                                                                                   (let
                                                                                                      ((_$1_17 i.0$1_0_old))
                                                                                                      (let
                                                                                                         ((_$1_18 (+ a$1_0_old _$1_17)))
                                                                                                         (let
                                                                                                            ((_$1_19 (select HEAP$1_old _$1_18))
                                                                                                             (_$1_20 j.0$1_0_old))
                                                                                                            (let
                                                                                                               ((_$1_21 (+ a$1_0_old _$1_20)))
                                                                                                               (let
                                                                                                                  ((_$1_22 (select HEAP$1_old _$1_21))
                                                                                                                   (_$1_23 i.0$1_0_old))
                                                                                                                  (let
                                                                                                                     ((_$1_24 (+ a$1_0_old _$1_23)))
                                                                                                                     (let
                                                                                                                        ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                                                                                         (_$1_25 j.0$1_0_old))
                                                                                                                        (let
                                                                                                                           ((_$1_26 (+ a$1_0_old _$1_25)))
                                                                                                                           (let
                                                                                                                              ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                                                                               (_$1_27 (+ j.0$1_0_old 1)))
                                                                                                                              (let
                                                                                                                                 ((j.0$1_0 _$1_27)
                                                                                                                                  (a$1_0 a$1_0_old)
                                                                                                                                  (i.0$1_0 i.0$1_0_old)
                                                                                                                                  (n$1_0 n$1_0_old))
                                                                                                                                 false)))))))))))))))))))
                                                                        (let
                                                                           ((_$1_6 (< j.0$1_0_old n$1_0_old)))
                                                                           (=>
                                                                              _$1_6
                                                                              (let
                                                                                 ((_$1_10 j.0$1_0_old))
                                                                                 (let
                                                                                    ((_$1_11 (+ a$1_0_old _$1_10)))
                                                                                    (let
                                                                                       ((_$1_12 (select HEAP$1_old _$1_11))
                                                                                        (_$1_13 i.0$1_0_old))
                                                                                       (let
                                                                                          ((_$1_14 (+ a$1_0_old _$1_13)))
                                                                                          (let
                                                                                             ((_$1_15 (select HEAP$1_old _$1_14)))
                                                                                             (let
                                                                                                ((_$1_16 (<= _$1_12 _$1_15)))
                                                                                                (=>
                                                                                                   (not _$1_16)
                                                                                                   (let
                                                                                                      ((_$1_27 (+ j.0$1_0_old 1)))
                                                                                                      (let
                                                                                                         ((j.0$1_0 _$1_27)
                                                                                                          (a$1_0 a$1_0_old)
                                                                                                          (i.0$1_0 i.0$1_0_old)
                                                                                                          (n$1_0 n$1_0_old))
                                                                                                         false))))))))))))
                                                                     (forall
                                                                        ((result$1 Int)
                                                                         (result$2 Int))
                                                                        (and
                                                                           (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0 i.0$2_0 j.0$2_0 n$2_0)
                                                                           (=>
                                                                              (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$1 result$2)
                                                                              (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old)
         (let
            ((_$2_6 (< j.0$2_0_old n$2_0_old)))
            (=>
               _$2_6
               (let
                  ((_$2_10 j.0$2_0_old))
                  (let
                     ((_$2_11 (+ a$2_0_old _$2_10)))
                     (let
                        ((_$2_12 (select HEAP$2_old _$2_11))
                         (_$2_13 i.0$2_0_old))
                        (let
                           ((_$2_14 (+ a$2_0_old _$2_13)))
                           (let
                              ((_$2_15 (select HEAP$2_old _$2_14)))
                              (let
                                 ((_$2_16 (< _$2_12 _$2_15)))
                                 (=>
                                    (not _$2_16)
                                    (let
                                       ((_$2_27 (+ j.0$2_0_old 1)))
                                       (let
                                          ((j.0$2_0 _$2_27)
                                           (a$2_0 a$2_0_old)
                                           (i.0$2_0 i.0$2_0_old)
                                           (n$2_0 n$2_0_old))
                                          (=>
                                             (and
                                                (let
                                                   ((_$1_6 (< j.0$1_0_old n$1_0_old)))
                                                   (=>
                                                      _$1_6
                                                      (let
                                                         ((_$1_10 j.0$1_0_old))
                                                         (let
                                                            ((_$1_11 (+ a$1_0_old _$1_10)))
                                                            (let
                                                               ((_$1_12 (select HEAP$1_old _$1_11))
                                                                (_$1_13 i.0$1_0_old))
                                                               (let
                                                                  ((_$1_14 (+ a$1_0_old _$1_13)))
                                                                  (let
                                                                     ((_$1_15 (select HEAP$1_old _$1_14)))
                                                                     (let
                                                                        ((_$1_16 (<= _$1_12 _$1_15)))
                                                                        (=>
                                                                           _$1_16
                                                                           (let
                                                                              ((_$1_17 i.0$1_0_old))
                                                                              (let
                                                                                 ((_$1_18 (+ a$1_0_old _$1_17)))
                                                                                 (let
                                                                                    ((_$1_19 (select HEAP$1_old _$1_18))
                                                                                     (_$1_20 j.0$1_0_old))
                                                                                    (let
                                                                                       ((_$1_21 (+ a$1_0_old _$1_20)))
                                                                                       (let
                                                                                          ((_$1_22 (select HEAP$1_old _$1_21))
                                                                                           (_$1_23 i.0$1_0_old))
                                                                                          (let
                                                                                             ((_$1_24 (+ a$1_0_old _$1_23)))
                                                                                             (let
                                                                                                ((HEAP$1 (store HEAP$1_old _$1_24 _$1_22))
                                                                                                 (_$1_25 j.0$1_0_old))
                                                                                                (let
                                                                                                   ((_$1_26 (+ a$1_0_old _$1_25)))
                                                                                                   (let
                                                                                                      ((HEAP$1 (store HEAP$1 _$1_26 _$1_19))
                                                                                                       (_$1_27 (+ j.0$1_0_old 1)))
                                                                                                      (let
                                                                                                         ((j.0$1_0 _$1_27)
                                                                                                          (a$1_0 a$1_0_old)
                                                                                                          (i.0$1_0 i.0$1_0_old)
                                                                                                          (n$1_0 n$1_0_old))
                                                                                                         false)))))))))))))))))))
                                                (let
                                                   ((_$1_6 (< j.0$1_0_old n$1_0_old)))
                                                   (=>
                                                      _$1_6
                                                      (let
                                                         ((_$1_10 j.0$1_0_old))
                                                         (let
                                                            ((_$1_11 (+ a$1_0_old _$1_10)))
                                                            (let
                                                               ((_$1_12 (select HEAP$1_old _$1_11))
                                                                (_$1_13 i.0$1_0_old))
                                                               (let
                                                                  ((_$1_14 (+ a$1_0_old _$1_13)))
                                                                  (let
                                                                     ((_$1_15 (select HEAP$1_old _$1_14)))
                                                                     (let
                                                                        ((_$1_16 (<= _$1_12 _$1_15)))
                                                                        (=>
                                                                           (not _$1_16)
                                                                           (let
                                                                              ((_$1_27 (+ j.0$1_0_old 1)))
                                                                              (let
                                                                                 ((j.0$1_0 _$1_27)
                                                                                  (a$1_0 a$1_0_old)
                                                                                  (i.0$1_0 i.0$1_0_old)
                                                                                  (n$1_0 n$1_0_old))
                                                                                 false))))))))))))
                                             (forall
                                                ((result$1 Int)
                                                 (result$2 Int))
                                                (and
                                                   (INV_2_PRE a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0 i.0$2_0 j.0$2_0 n$2_0)
                                                   (=>
                                                      (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0 i.0$2_0 j.0$2_0 n$2_0 result$1 result$2)
                                                      (INV_2 a$1_0_old i.0$1_0_old j.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old j.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))
(check-sat)
(get-model)
