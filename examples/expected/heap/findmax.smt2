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
   INV_42_MAIN
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
   INV_REC_findmax
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_findmax_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_findmax__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_findmax__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_findmax__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_findmax__2_PRE
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
    Int
    Int)
   Bool)
(declare-fun
   INV_42__2_PRE
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
            ((i.0$1_0 1)
             (max.0$1_0 0)
             (a$1_0 a$1_0_old)
             (n$1_0 n$1_0_old)
             (_$2_0 (+ a$2_0_old 0)))
            (let
               ((_$2_1 (select HEAP$2_old _$2_0)))
               (let
                  ((i.0$2_0 1)
                   (maxv.0$2_0 _$2_1)
                   (a$2_0 a$2_0_old)
                   (n$2_0 n$2_0_old))
                  (INV_42_MAIN a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((_$1_13 max.0$1_0_old))
                  (let
                     ((_$1_14 (+ a$1_0_old _$1_13)))
                     (let
                        ((_$1_15 (select HEAP$1_old _$1_14)))
                        (let
                           ((result$1 _$1_15)
                            (_$2_3 (< i.0$2_0_old n$2_0_old)))
                           (=>
                              (not _$2_3)
                              (let
                                 ((result$2 maxv.0$2_0_old))
                                 (OUT_INV
                                    result$1
                                    result$2))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    _$1_11
                                    (let
                                       ((max.1$1_0 i.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_3 (< i.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 i.0$2_0_old))
                                                (let
                                                   ((_$2_8 (+ a$2_0_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (select HEAP$2_old _$2_8)))
                                                      (let
                                                         ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                         (=>
                                                            _$2_10
                                                            (let
                                                               ((_$2_11 i.0$2_0_old))
                                                               (let
                                                                  ((_$2_12 (+ a$2_0_old _$2_11)))
                                                                  (let
                                                                     ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                     (let
                                                                        ((maxv.1$2_0 _$2_13)
                                                                         (_$2_14 (+ i.0$2_0_old 1)))
                                                                        (let
                                                                           ((i.0$2_0 _$2_14)
                                                                            (maxv.0$2_0 maxv.1$2_0)
                                                                            (a$2_0 a$2_0_old)
                                                                            (n$2_0 n$2_0_old))
                                                                           (INV_42_MAIN a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    _$1_11
                                    (let
                                       ((max.1$1_0 i.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_3 (< i.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 i.0$2_0_old))
                                                (let
                                                   ((_$2_8 (+ a$2_0_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (select HEAP$2_old _$2_8)))
                                                      (let
                                                         ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                         (=>
                                                            (not _$2_10)
                                                            (let
                                                               ((maxv.1$2_0 maxv.0$2_0_old)
                                                                (_$2_14 (+ i.0$2_0_old 1)))
                                                               (let
                                                                  ((i.0$2_0 _$2_14)
                                                                   (maxv.0$2_0 maxv.1$2_0)
                                                                   (a$2_0 a$2_0_old)
                                                                   (n$2_0 n$2_0_old))
                                                                  (INV_42_MAIN a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    (not _$1_11)
                                    (let
                                       ((max.1$1_0 max.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_3 (< i.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 i.0$2_0_old))
                                                (let
                                                   ((_$2_8 (+ a$2_0_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (select HEAP$2_old _$2_8)))
                                                      (let
                                                         ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                         (=>
                                                            _$2_10
                                                            (let
                                                               ((_$2_11 i.0$2_0_old))
                                                               (let
                                                                  ((_$2_12 (+ a$2_0_old _$2_11)))
                                                                  (let
                                                                     ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                     (let
                                                                        ((maxv.1$2_0 _$2_13)
                                                                         (_$2_14 (+ i.0$2_0_old 1)))
                                                                        (let
                                                                           ((i.0$2_0 _$2_14)
                                                                            (maxv.0$2_0 maxv.1$2_0)
                                                                            (a$2_0 a$2_0_old)
                                                                            (n$2_0 n$2_0_old))
                                                                           (INV_42_MAIN a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    (not _$1_11)
                                    (let
                                       ((max.1$1_0 max.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_3 (< i.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 i.0$2_0_old))
                                                (let
                                                   ((_$2_8 (+ a$2_0_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (select HEAP$2_old _$2_8)))
                                                      (let
                                                         ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                         (=>
                                                            (not _$2_10)
                                                            (let
                                                               ((maxv.1$2_0 maxv.0$2_0_old)
                                                                (_$2_14 (+ i.0$2_0_old 1)))
                                                               (let
                                                                  ((i.0$2_0 _$2_14)
                                                                   (maxv.0$2_0 maxv.1$2_0)
                                                                   (a$2_0 a$2_0_old)
                                                                   (n$2_0 n$2_0_old))
                                                                  (INV_42_MAIN a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)))))))))))))))))))))))
; forbidden main
; offbyn main
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    _$1_11
                                    (let
                                       ((max.1$1_0 i.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old))
                                          (=>
                                             (and
                                                (let
                                                   ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_3
                                                      (let
                                                         ((_$2_7 i.0$2_0_old))
                                                         (let
                                                            ((_$2_8 (+ a$2_0_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (select HEAP$2_old _$2_8)))
                                                               (let
                                                                  ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                                  (=>
                                                                     _$2_10
                                                                     (let
                                                                        ((_$2_11 i.0$2_0_old))
                                                                        (let
                                                                           ((_$2_12 (+ a$2_0_old _$2_11)))
                                                                           (let
                                                                              ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                              (let
                                                                                 ((maxv.1$2_0 _$2_13)
                                                                                  (_$2_14 (+ i.0$2_0_old 1)))
                                                                                 (let
                                                                                    ((i.0$2_0 _$2_14)
                                                                                     (maxv.0$2_0 maxv.1$2_0)
                                                                                     (a$2_0 a$2_0_old)
                                                                                     (n$2_0 n$2_0_old))
                                                                                    false))))))))))))
                                                (let
                                                   ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_3
                                                      (let
                                                         ((_$2_7 i.0$2_0_old))
                                                         (let
                                                            ((_$2_8 (+ a$2_0_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (select HEAP$2_old _$2_8)))
                                                               (let
                                                                  ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                                  (=>
                                                                     (not _$2_10)
                                                                     (let
                                                                        ((maxv.1$2_0 maxv.0$2_0_old)
                                                                         (_$2_14 (+ i.0$2_0_old 1)))
                                                                        (let
                                                                           ((i.0$2_0 _$2_14)
                                                                            (maxv.0$2_0 maxv.1$2_0)
                                                                            (a$2_0 a$2_0_old)
                                                                            (n$2_0 n$2_0_old))
                                                                           false))))))))))
                                             (INV_42_MAIN a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    (not _$1_11)
                                    (let
                                       ((max.1$1_0 max.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old))
                                          (=>
                                             (and
                                                (let
                                                   ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_3
                                                      (let
                                                         ((_$2_7 i.0$2_0_old))
                                                         (let
                                                            ((_$2_8 (+ a$2_0_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (select HEAP$2_old _$2_8)))
                                                               (let
                                                                  ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                                  (=>
                                                                     _$2_10
                                                                     (let
                                                                        ((_$2_11 i.0$2_0_old))
                                                                        (let
                                                                           ((_$2_12 (+ a$2_0_old _$2_11)))
                                                                           (let
                                                                              ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                              (let
                                                                                 ((maxv.1$2_0 _$2_13)
                                                                                  (_$2_14 (+ i.0$2_0_old 1)))
                                                                                 (let
                                                                                    ((i.0$2_0 _$2_14)
                                                                                     (maxv.0$2_0 maxv.1$2_0)
                                                                                     (a$2_0 a$2_0_old)
                                                                                     (n$2_0 n$2_0_old))
                                                                                    false))))))))))))
                                                (let
                                                   ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_3
                                                      (let
                                                         ((_$2_7 i.0$2_0_old))
                                                         (let
                                                            ((_$2_8 (+ a$2_0_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (select HEAP$2_old _$2_8)))
                                                               (let
                                                                  ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                                  (=>
                                                                     (not _$2_10)
                                                                     (let
                                                                        ((maxv.1$2_0 maxv.0$2_0_old)
                                                                         (_$2_14 (+ i.0$2_0_old 1)))
                                                                        (let
                                                                           ((i.0$2_0 _$2_14)
                                                                            (maxv.0$2_0 maxv.1$2_0)
                                                                            (a$2_0 a$2_0_old)
                                                                            (n$2_0 n$2_0_old))
                                                                           false))))))))))
                                             (INV_42_MAIN a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 i.0$2_0_old))
                  (let
                     ((_$2_8 (+ a$2_0_old _$2_7)))
                     (let
                        ((_$2_9 (select HEAP$2_old _$2_8)))
                        (let
                           ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                           (=>
                              _$2_10
                              (let
                                 ((_$2_11 i.0$2_0_old))
                                 (let
                                    ((_$2_12 (+ a$2_0_old _$2_11)))
                                    (let
                                       ((_$2_13 (select HEAP$2_old _$2_12)))
                                       (let
                                          ((maxv.1$2_0 _$2_13)
                                           (_$2_14 (+ i.0$2_0_old 1)))
                                          (let
                                             ((i.0$2_0 _$2_14)
                                              (maxv.0$2_0 maxv.1$2_0)
                                              (a$2_0 a$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (=>
                                                (and
                                                   (let
                                                      ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                                      (=>
                                                         _$1_1
                                                         (let
                                                            ((_$1_5 i.0$1_0_old))
                                                            (let
                                                               ((_$1_6 (+ a$1_0_old _$1_5)))
                                                               (let
                                                                  ((_$1_7 (select HEAP$1_old _$1_6))
                                                                   (_$1_8 max.0$1_0_old))
                                                                  (let
                                                                     ((_$1_9 (+ a$1_0_old _$1_8)))
                                                                     (let
                                                                        ((_$1_10 (select HEAP$1_old _$1_9)))
                                                                        (let
                                                                           ((_$1_11 (>= _$1_7 _$1_10)))
                                                                           (=>
                                                                              _$1_11
                                                                              (let
                                                                                 ((max.1$1_0 i.0$1_0_old)
                                                                                  (_$1_12 (+ i.0$1_0_old 1)))
                                                                                 (let
                                                                                    ((i.0$1_0 _$1_12)
                                                                                     (max.0$1_0 max.1$1_0)
                                                                                     (a$1_0 a$1_0_old)
                                                                                     (n$1_0 n$1_0_old))
                                                                                    false)))))))))))
                                                   (let
                                                      ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                                      (=>
                                                         _$1_1
                                                         (let
                                                            ((_$1_5 i.0$1_0_old))
                                                            (let
                                                               ((_$1_6 (+ a$1_0_old _$1_5)))
                                                               (let
                                                                  ((_$1_7 (select HEAP$1_old _$1_6))
                                                                   (_$1_8 max.0$1_0_old))
                                                                  (let
                                                                     ((_$1_9 (+ a$1_0_old _$1_8)))
                                                                     (let
                                                                        ((_$1_10 (select HEAP$1_old _$1_9)))
                                                                        (let
                                                                           ((_$1_11 (>= _$1_7 _$1_10)))
                                                                           (=>
                                                                              (not _$1_11)
                                                                              (let
                                                                                 ((max.1$1_0 max.0$1_0_old)
                                                                                  (_$1_12 (+ i.0$1_0_old 1)))
                                                                                 (let
                                                                                    ((i.0$1_0 _$1_12)
                                                                                     (max.0$1_0 max.1$1_0)
                                                                                     (a$1_0 a$1_0_old)
                                                                                     (n$1_0 n$1_0_old))
                                                                                    false))))))))))))
                                                (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 i.0$2_0_old))
                  (let
                     ((_$2_8 (+ a$2_0_old _$2_7)))
                     (let
                        ((_$2_9 (select HEAP$2_old _$2_8)))
                        (let
                           ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                           (=>
                              (not _$2_10)
                              (let
                                 ((maxv.1$2_0 maxv.0$2_0_old)
                                  (_$2_14 (+ i.0$2_0_old 1)))
                                 (let
                                    ((i.0$2_0 _$2_14)
                                     (maxv.0$2_0 maxv.1$2_0)
                                     (a$2_0 a$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (=>
                                       (and
                                          (let
                                             ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                             (=>
                                                _$1_1
                                                (let
                                                   ((_$1_5 i.0$1_0_old))
                                                   (let
                                                      ((_$1_6 (+ a$1_0_old _$1_5)))
                                                      (let
                                                         ((_$1_7 (select HEAP$1_old _$1_6))
                                                          (_$1_8 max.0$1_0_old))
                                                         (let
                                                            ((_$1_9 (+ a$1_0_old _$1_8)))
                                                            (let
                                                               ((_$1_10 (select HEAP$1_old _$1_9)))
                                                               (let
                                                                  ((_$1_11 (>= _$1_7 _$1_10)))
                                                                  (=>
                                                                     _$1_11
                                                                     (let
                                                                        ((max.1$1_0 i.0$1_0_old)
                                                                         (_$1_12 (+ i.0$1_0_old 1)))
                                                                        (let
                                                                           ((i.0$1_0 _$1_12)
                                                                            (max.0$1_0 max.1$1_0)
                                                                            (a$1_0 a$1_0_old)
                                                                            (n$1_0 n$1_0_old))
                                                                           false)))))))))))
                                          (let
                                             ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                             (=>
                                                _$1_1
                                                (let
                                                   ((_$1_5 i.0$1_0_old))
                                                   (let
                                                      ((_$1_6 (+ a$1_0_old _$1_5)))
                                                      (let
                                                         ((_$1_7 (select HEAP$1_old _$1_6))
                                                          (_$1_8 max.0$1_0_old))
                                                         (let
                                                            ((_$1_9 (+ a$1_0_old _$1_8)))
                                                            (let
                                                               ((_$1_10 (select HEAP$1_old _$1_9)))
                                                               (let
                                                                  ((_$1_11 (>= _$1_7 _$1_10)))
                                                                  (=>
                                                                     (not _$1_11)
                                                                     (let
                                                                        ((max.1$1_0 max.0$1_0_old)
                                                                         (_$1_12 (+ i.0$1_0_old 1)))
                                                                        (let
                                                                           ((i.0$1_0 _$1_12)
                                                                            (max.0$1_0 max.1$1_0)
                                                                            (a$1_0 a$1_0_old)
                                                                            (n$1_0 n$1_0_old))
                                                                           false))))))))))))
                                       (INV_42_MAIN a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0 i.0$2_0 maxv.0$2_0 n$2_0))))))))))))))
; end
(assert
   (forall
      ((a$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_findmax_PRE a$1_0_old n$1_0_old a$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 1)
             (max.0$1_0 0)
             (a$1_0 a$1_0_old)
             (n$1_0 n$1_0_old)
             (_$2_0 (+ a$2_0_old 0)))
            (let
               ((_$2_1 (select HEAP$2_old _$2_0)))
               (let
                  ((i.0$2_0 1)
                   (maxv.0$2_0 _$2_1)
                   (a$2_0 a$2_0_old)
                   (n$2_0 n$2_0_old))
                  (forall
                     ((result$1 Int)
                      (result$2 Int))
                     (and
                        (INV_42_PRE a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)
                        (=>
                           (INV_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$1 result$2)
                           (INV_REC_findmax a$1_0_old n$1_0_old a$2_0_old n$2_0_old result$1 result$2))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((_$1_13 max.0$1_0_old))
                  (let
                     ((_$1_14 (+ a$1_0_old _$1_13)))
                     (let
                        ((_$1_15 (select HEAP$1_old _$1_14)))
                        (let
                           ((result$1 _$1_15)
                            (_$2_3 (< i.0$2_0_old n$2_0_old)))
                           (=>
                              (not _$2_3)
                              (let
                                 ((result$2 maxv.0$2_0_old))
                                 (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    _$1_11
                                    (let
                                       ((max.1$1_0 i.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_3 (< i.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 i.0$2_0_old))
                                                (let
                                                   ((_$2_8 (+ a$2_0_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (select HEAP$2_old _$2_8)))
                                                      (let
                                                         ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                         (=>
                                                            _$2_10
                                                            (let
                                                               ((_$2_11 i.0$2_0_old))
                                                               (let
                                                                  ((_$2_12 (+ a$2_0_old _$2_11)))
                                                                  (let
                                                                     ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                     (let
                                                                        ((maxv.1$2_0 _$2_13)
                                                                         (_$2_14 (+ i.0$2_0_old 1)))
                                                                        (let
                                                                           ((i.0$2_0 _$2_14)
                                                                            (maxv.0$2_0 maxv.1$2_0)
                                                                            (a$2_0 a$2_0_old)
                                                                            (n$2_0 n$2_0_old))
                                                                           (forall
                                                                              ((result$1 Int)
                                                                               (result$2 Int))
                                                                              (and
                                                                                 (INV_42_PRE a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)
                                                                                 (=>
                                                                                    (INV_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$1 result$2)
                                                                                    (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    _$1_11
                                    (let
                                       ((max.1$1_0 i.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_3 (< i.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 i.0$2_0_old))
                                                (let
                                                   ((_$2_8 (+ a$2_0_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (select HEAP$2_old _$2_8)))
                                                      (let
                                                         ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                         (=>
                                                            (not _$2_10)
                                                            (let
                                                               ((maxv.1$2_0 maxv.0$2_0_old)
                                                                (_$2_14 (+ i.0$2_0_old 1)))
                                                               (let
                                                                  ((i.0$2_0 _$2_14)
                                                                   (maxv.0$2_0 maxv.1$2_0)
                                                                   (a$2_0 a$2_0_old)
                                                                   (n$2_0 n$2_0_old))
                                                                  (forall
                                                                     ((result$1 Int)
                                                                      (result$2 Int))
                                                                     (and
                                                                        (INV_42_PRE a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)
                                                                        (=>
                                                                           (INV_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$1 result$2)
                                                                           (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    (not _$1_11)
                                    (let
                                       ((max.1$1_0 max.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_3 (< i.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 i.0$2_0_old))
                                                (let
                                                   ((_$2_8 (+ a$2_0_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (select HEAP$2_old _$2_8)))
                                                      (let
                                                         ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                         (=>
                                                            _$2_10
                                                            (let
                                                               ((_$2_11 i.0$2_0_old))
                                                               (let
                                                                  ((_$2_12 (+ a$2_0_old _$2_11)))
                                                                  (let
                                                                     ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                     (let
                                                                        ((maxv.1$2_0 _$2_13)
                                                                         (_$2_14 (+ i.0$2_0_old 1)))
                                                                        (let
                                                                           ((i.0$2_0 _$2_14)
                                                                            (maxv.0$2_0 maxv.1$2_0)
                                                                            (a$2_0 a$2_0_old)
                                                                            (n$2_0 n$2_0_old))
                                                                           (forall
                                                                              ((result$1 Int)
                                                                               (result$2 Int))
                                                                              (and
                                                                                 (INV_42_PRE a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)
                                                                                 (=>
                                                                                    (INV_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$1 result$2)
                                                                                    (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    (not _$1_11)
                                    (let
                                       ((max.1$1_0 max.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old)
                                           (_$2_3 (< i.0$2_0_old n$2_0_old)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 i.0$2_0_old))
                                                (let
                                                   ((_$2_8 (+ a$2_0_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (select HEAP$2_old _$2_8)))
                                                      (let
                                                         ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                         (=>
                                                            (not _$2_10)
                                                            (let
                                                               ((maxv.1$2_0 maxv.0$2_0_old)
                                                                (_$2_14 (+ i.0$2_0_old 1)))
                                                               (let
                                                                  ((i.0$2_0 _$2_14)
                                                                   (maxv.0$2_0 maxv.1$2_0)
                                                                   (a$2_0 a$2_0_old)
                                                                   (n$2_0 n$2_0_old))
                                                                  (forall
                                                                     ((result$1 Int)
                                                                      (result$2 Int))
                                                                     (and
                                                                        (INV_42_PRE a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)
                                                                        (=>
                                                                           (INV_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$1 result$2)
                                                                           (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_findmax__1_PRE a$1_0_old n$1_0_old)
         (let
            ((i.0$1_0 1)
             (max.0$1_0 0)
             (a$1_0 a$1_0_old)
             (n$1_0 n$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_42__1 a$1_0 i.0$1_0 max.0$1_0 n$1_0 result$1)
                  (INV_REC_findmax__1 a$1_0_old n$1_0_old result$1)))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((_$1_13 max.0$1_0_old))
                  (let
                     ((_$1_14 (+ a$1_0_old _$1_13)))
                     (let
                        ((_$1_15 (select HEAP$1_old _$1_14)))
                        (let
                           ((result$1 _$1_15))
                           (INV_42__1 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old result$1))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    _$1_11
                                    (let
                                       ((max.1$1_0 i.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old))
                                          (forall
                                             ((result$1 Int))
                                             (=>
                                                (INV_42__1 a$1_0 i.0$1_0 max.0$1_0 n$1_0 result$1)
                                                (INV_42__1 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old result$1)))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    (not _$1_11)
                                    (let
                                       ((max.1$1_0 max.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old))
                                          (forall
                                             ((result$1 Int))
                                             (=>
                                                (INV_42__1 a$1_0 i.0$1_0 max.0$1_0 n$1_0 result$1)
                                                (INV_42__1 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old result$1)))))))))))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_findmax__2_PRE a$2_0_old n$2_0_old)
         (let
            ((_$2_0 (+ a$2_0_old 0)))
            (let
               ((_$2_1 (select HEAP$2_old _$2_0)))
               (let
                  ((i.0$2_0 1)
                   (maxv.0$2_0 _$2_1)
                   (a$2_0 a$2_0_old)
                   (n$2_0 n$2_0_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_42__2 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$2)
                        (INV_REC_findmax__2 a$2_0_old n$2_0_old result$2)))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               (not _$2_3)
               (let
                  ((result$2 maxv.0$2_0_old))
                  (INV_42__2 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$2)))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 i.0$2_0_old))
                  (let
                     ((_$2_8 (+ a$2_0_old _$2_7)))
                     (let
                        ((_$2_9 (select HEAP$2_old _$2_8)))
                        (let
                           ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                           (=>
                              _$2_10
                              (let
                                 ((_$2_11 i.0$2_0_old))
                                 (let
                                    ((_$2_12 (+ a$2_0_old _$2_11)))
                                    (let
                                       ((_$2_13 (select HEAP$2_old _$2_12)))
                                       (let
                                          ((maxv.1$2_0 _$2_13)
                                           (_$2_14 (+ i.0$2_0_old 1)))
                                          (let
                                             ((i.0$2_0 _$2_14)
                                              (maxv.0$2_0 maxv.1$2_0)
                                              (a$2_0 a$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (forall
                                                ((result$2 Int))
                                                (=>
                                                   (INV_42__2 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$2)
                                                   (INV_42__2 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$2))))))))))))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 i.0$2_0_old))
                  (let
                     ((_$2_8 (+ a$2_0_old _$2_7)))
                     (let
                        ((_$2_9 (select HEAP$2_old _$2_8)))
                        (let
                           ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                           (=>
                              (not _$2_10)
                              (let
                                 ((maxv.1$2_0 maxv.0$2_0_old)
                                  (_$2_14 (+ i.0$2_0_old 1)))
                                 (let
                                    ((i.0$2_0 _$2_14)
                                     (maxv.0$2_0 maxv.1$2_0)
                                     (a$2_0 a$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (forall
                                       ((result$2 Int))
                                       (=>
                                          (INV_42__2 a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$2)
                                          (INV_42__2 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$2)))))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    _$1_11
                                    (let
                                       ((max.1$1_0 i.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old))
                                          (=>
                                             (and
                                                (let
                                                   ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_3
                                                      (let
                                                         ((_$2_7 i.0$2_0_old))
                                                         (let
                                                            ((_$2_8 (+ a$2_0_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (select HEAP$2_old _$2_8)))
                                                               (let
                                                                  ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                                  (=>
                                                                     _$2_10
                                                                     (let
                                                                        ((_$2_11 i.0$2_0_old))
                                                                        (let
                                                                           ((_$2_12 (+ a$2_0_old _$2_11)))
                                                                           (let
                                                                              ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                              (let
                                                                                 ((maxv.1$2_0 _$2_13)
                                                                                  (_$2_14 (+ i.0$2_0_old 1)))
                                                                                 (let
                                                                                    ((i.0$2_0 _$2_14)
                                                                                     (maxv.0$2_0 maxv.1$2_0)
                                                                                     (a$2_0 a$2_0_old)
                                                                                     (n$2_0 n$2_0_old))
                                                                                    false))))))))))))
                                                (let
                                                   ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_3
                                                      (let
                                                         ((_$2_7 i.0$2_0_old))
                                                         (let
                                                            ((_$2_8 (+ a$2_0_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (select HEAP$2_old _$2_8)))
                                                               (let
                                                                  ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                                  (=>
                                                                     (not _$2_10)
                                                                     (let
                                                                        ((maxv.1$2_0 maxv.0$2_0_old)
                                                                         (_$2_14 (+ i.0$2_0_old 1)))
                                                                        (let
                                                                           ((i.0$2_0 _$2_14)
                                                                            (maxv.0$2_0 maxv.1$2_0)
                                                                            (a$2_0 a$2_0_old)
                                                                            (n$2_0 n$2_0_old))
                                                                           false))))))))))
                                             (forall
                                                ((result$1 Int)
                                                 (result$2 Int))
                                                (and
                                                   (INV_42_PRE a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
                                                   (=>
                                                      (INV_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2)
                                                      (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ a$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 max.0$1_0_old))
                        (let
                           ((_$1_9 (+ a$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9)))
                              (let
                                 ((_$1_11 (>= _$1_7 _$1_10)))
                                 (=>
                                    (not _$1_11)
                                    (let
                                       ((max.1$1_0 max.0$1_0_old)
                                        (_$1_12 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_12)
                                           (max.0$1_0 max.1$1_0)
                                           (a$1_0 a$1_0_old)
                                           (n$1_0 n$1_0_old))
                                          (=>
                                             (and
                                                (let
                                                   ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_3
                                                      (let
                                                         ((_$2_7 i.0$2_0_old))
                                                         (let
                                                            ((_$2_8 (+ a$2_0_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (select HEAP$2_old _$2_8)))
                                                               (let
                                                                  ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                                  (=>
                                                                     _$2_10
                                                                     (let
                                                                        ((_$2_11 i.0$2_0_old))
                                                                        (let
                                                                           ((_$2_12 (+ a$2_0_old _$2_11)))
                                                                           (let
                                                                              ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                              (let
                                                                                 ((maxv.1$2_0 _$2_13)
                                                                                  (_$2_14 (+ i.0$2_0_old 1)))
                                                                                 (let
                                                                                    ((i.0$2_0 _$2_14)
                                                                                     (maxv.0$2_0 maxv.1$2_0)
                                                                                     (a$2_0 a$2_0_old)
                                                                                     (n$2_0 n$2_0_old))
                                                                                    false))))))))))))
                                                (let
                                                   ((_$2_3 (< i.0$2_0_old n$2_0_old)))
                                                   (=>
                                                      _$2_3
                                                      (let
                                                         ((_$2_7 i.0$2_0_old))
                                                         (let
                                                            ((_$2_8 (+ a$2_0_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (select HEAP$2_old _$2_8)))
                                                               (let
                                                                  ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                                                                  (=>
                                                                     (not _$2_10)
                                                                     (let
                                                                        ((maxv.1$2_0 maxv.0$2_0_old)
                                                                         (_$2_14 (+ i.0$2_0_old 1)))
                                                                        (let
                                                                           ((i.0$2_0 _$2_14)
                                                                            (maxv.0$2_0 maxv.1$2_0)
                                                                            (a$2_0 a$2_0_old)
                                                                            (n$2_0 n$2_0_old))
                                                                           false))))))))))
                                             (forall
                                                ((result$1 Int)
                                                 (result$2 Int))
                                                (and
                                                   (INV_42_PRE a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
                                                   (=>
                                                      (INV_42 a$1_0 i.0$1_0 max.0$1_0 n$1_0 a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2)
                                                      (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 i.0$2_0_old))
                  (let
                     ((_$2_8 (+ a$2_0_old _$2_7)))
                     (let
                        ((_$2_9 (select HEAP$2_old _$2_8)))
                        (let
                           ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                           (=>
                              _$2_10
                              (let
                                 ((_$2_11 i.0$2_0_old))
                                 (let
                                    ((_$2_12 (+ a$2_0_old _$2_11)))
                                    (let
                                       ((_$2_13 (select HEAP$2_old _$2_12)))
                                       (let
                                          ((maxv.1$2_0 _$2_13)
                                           (_$2_14 (+ i.0$2_0_old 1)))
                                          (let
                                             ((i.0$2_0 _$2_14)
                                              (maxv.0$2_0 maxv.1$2_0)
                                              (a$2_0 a$2_0_old)
                                              (n$2_0 n$2_0_old))
                                             (=>
                                                (and
                                                   (let
                                                      ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                                      (=>
                                                         _$1_1
                                                         (let
                                                            ((_$1_5 i.0$1_0_old))
                                                            (let
                                                               ((_$1_6 (+ a$1_0_old _$1_5)))
                                                               (let
                                                                  ((_$1_7 (select HEAP$1_old _$1_6))
                                                                   (_$1_8 max.0$1_0_old))
                                                                  (let
                                                                     ((_$1_9 (+ a$1_0_old _$1_8)))
                                                                     (let
                                                                        ((_$1_10 (select HEAP$1_old _$1_9)))
                                                                        (let
                                                                           ((_$1_11 (>= _$1_7 _$1_10)))
                                                                           (=>
                                                                              _$1_11
                                                                              (let
                                                                                 ((max.1$1_0 i.0$1_0_old)
                                                                                  (_$1_12 (+ i.0$1_0_old 1)))
                                                                                 (let
                                                                                    ((i.0$1_0 _$1_12)
                                                                                     (max.0$1_0 max.1$1_0)
                                                                                     (a$1_0 a$1_0_old)
                                                                                     (n$1_0 n$1_0_old))
                                                                                    false)))))))))))
                                                   (let
                                                      ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                                      (=>
                                                         _$1_1
                                                         (let
                                                            ((_$1_5 i.0$1_0_old))
                                                            (let
                                                               ((_$1_6 (+ a$1_0_old _$1_5)))
                                                               (let
                                                                  ((_$1_7 (select HEAP$1_old _$1_6))
                                                                   (_$1_8 max.0$1_0_old))
                                                                  (let
                                                                     ((_$1_9 (+ a$1_0_old _$1_8)))
                                                                     (let
                                                                        ((_$1_10 (select HEAP$1_old _$1_9)))
                                                                        (let
                                                                           ((_$1_11 (>= _$1_7 _$1_10)))
                                                                           (=>
                                                                              (not _$1_11)
                                                                              (let
                                                                                 ((max.1$1_0 max.0$1_0_old)
                                                                                  (_$1_12 (+ i.0$1_0_old 1)))
                                                                                 (let
                                                                                    ((i.0$1_0 _$1_12)
                                                                                     (max.0$1_0 max.1$1_0)
                                                                                     (a$1_0 a$1_0_old)
                                                                                     (n$1_0 n$1_0_old))
                                                                                    false))))))))))))
                                                (forall
                                                   ((result$1 Int)
                                                    (result$2 Int))
                                                   (and
                                                      (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)
                                                      (=>
                                                         (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$1 result$2)
                                                         (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (i.0$2_0_old Int)
       (maxv.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old)
         (let
            ((_$2_3 (< i.0$2_0_old n$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 i.0$2_0_old))
                  (let
                     ((_$2_8 (+ a$2_0_old _$2_7)))
                     (let
                        ((_$2_9 (select HEAP$2_old _$2_8)))
                        (let
                           ((_$2_10 (>= _$2_9 maxv.0$2_0_old)))
                           (=>
                              (not _$2_10)
                              (let
                                 ((maxv.1$2_0 maxv.0$2_0_old)
                                  (_$2_14 (+ i.0$2_0_old 1)))
                                 (let
                                    ((i.0$2_0 _$2_14)
                                     (maxv.0$2_0 maxv.1$2_0)
                                     (a$2_0 a$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (=>
                                       (and
                                          (let
                                             ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                             (=>
                                                _$1_1
                                                (let
                                                   ((_$1_5 i.0$1_0_old))
                                                   (let
                                                      ((_$1_6 (+ a$1_0_old _$1_5)))
                                                      (let
                                                         ((_$1_7 (select HEAP$1_old _$1_6))
                                                          (_$1_8 max.0$1_0_old))
                                                         (let
                                                            ((_$1_9 (+ a$1_0_old _$1_8)))
                                                            (let
                                                               ((_$1_10 (select HEAP$1_old _$1_9)))
                                                               (let
                                                                  ((_$1_11 (>= _$1_7 _$1_10)))
                                                                  (=>
                                                                     _$1_11
                                                                     (let
                                                                        ((max.1$1_0 i.0$1_0_old)
                                                                         (_$1_12 (+ i.0$1_0_old 1)))
                                                                        (let
                                                                           ((i.0$1_0 _$1_12)
                                                                            (max.0$1_0 max.1$1_0)
                                                                            (a$1_0 a$1_0_old)
                                                                            (n$1_0 n$1_0_old))
                                                                           false)))))))))))
                                          (let
                                             ((_$1_1 (< i.0$1_0_old n$1_0_old)))
                                             (=>
                                                _$1_1
                                                (let
                                                   ((_$1_5 i.0$1_0_old))
                                                   (let
                                                      ((_$1_6 (+ a$1_0_old _$1_5)))
                                                      (let
                                                         ((_$1_7 (select HEAP$1_old _$1_6))
                                                          (_$1_8 max.0$1_0_old))
                                                         (let
                                                            ((_$1_9 (+ a$1_0_old _$1_8)))
                                                            (let
                                                               ((_$1_10 (select HEAP$1_old _$1_9)))
                                                               (let
                                                                  ((_$1_11 (>= _$1_7 _$1_10)))
                                                                  (=>
                                                                     (not _$1_11)
                                                                     (let
                                                                        ((max.1$1_0 max.0$1_0_old)
                                                                         (_$1_12 (+ i.0$1_0_old 1)))
                                                                        (let
                                                                           ((i.0$1_0 _$1_12)
                                                                            (max.0$1_0 max.1$1_0)
                                                                            (a$1_0 a$1_0_old)
                                                                            (n$1_0 n$1_0_old))
                                                                           false))))))))))))
                                       (forall
                                          ((result$1 Int)
                                           (result$2 Int))
                                          (and
                                             (INV_42_PRE a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0 i.0$2_0 maxv.0$2_0 n$2_0)
                                             (=>
                                                (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0 i.0$2_0 maxv.0$2_0 n$2_0 result$1 result$2)
                                                (INV_42 a$1_0_old i.0$1_0_old max.0$1_0_old n$1_0_old a$2_0_old i.0$2_0_old maxv.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))))
(check-sat)
(get-model)
