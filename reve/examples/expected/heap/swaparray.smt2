(set-logic HORN)
(define-fun
   IN_INV
   ((a$1_0 Int)
    (b$1_0 Int)
    (n$1_0 Int)
    (a$2_0 Int)
    (b$2_0 Int)
    (n$2_0 Int))
   Bool
   (and (= a$1_0 a$2_0) (= b$1_0 b$2_0) (= n$1_0 n$2_0) (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i))) (> a$1_0 (+ b$1_0 n$1_0))))
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
   INV_REC_swap
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
   INV_REC_swap_PRE
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_swap__1
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_swap__1_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_swap__2
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_swap__2_PRE
   (Int
    Int
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
       (b$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (b$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            a$1_0_old
            b$1_0_old
            n$1_0_old
            a$2_0_old
            b$2_0_old
            n$2_0_old)
         (let
            ((i.0$1_0 0)
             (a$1_0 a$1_0_old)
             (b$1_0 b$1_0_old)
             (n$1_0 n$1_0_old)
             (.01$2_0 b$2_0_old)
             (.0$2_0 a$2_0_old)
             (a$2_0 a$2_0_old)
             (n$2_0 n$2_0_old))
            (INV_42_MAIN a$1_0 b$1_0 i.0$1_0 n$1_0 .0$2_0 .01$2_0 a$2_0 n$2_0)))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 0)
                   (_$2_1 .0$2_0_old)
                   (_$2_2 a$2_0_old))
                  (let
                     ((_$2_3 (- _$2_1 _$2_2)))
                     (let
                        ((_$2_4 _$2_3)
                         (_$2_5 n$2_0_old))
                        (let
                           ((_$2_6 (< _$2_4 _$2_5)))
                           (=>
                              (not _$2_6)
                              (let
                                 ((result$2 0))
                                 (OUT_INV
                                    result$1
                                    result$2))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
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
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ b$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9))
                               (_$1_11 i.0$1_0_old))
                              (let
                                 ((_$1_12 (+ a$1_0_old _$1_11)))
                                 (let
                                    ((HEAP$1 (store HEAP$1_old _$1_12 _$1_10))
                                     (_$1_13 i.0$1_0_old))
                                    (let
                                       ((_$1_14 (+ b$1_0_old _$1_13)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 _$1_14 _$1_7))
                                           (_$1_15 (+ i.0$1_0_old 1)))
                                          (let
                                             ((i.0$1_0 _$1_15)
                                              (a$1_0 a$1_0_old)
                                              (b$1_0 b$1_0_old)
                                              (n$1_0 n$1_0_old)
                                              (_$2_1 .0$2_0_old)
                                              (_$2_2 a$2_0_old))
                                             (let
                                                ((_$2_3 (- _$2_1 _$2_2)))
                                                (let
                                                   ((_$2_4 _$2_3)
                                                    (_$2_5 n$2_0_old))
                                                   (let
                                                      ((_$2_6 (< _$2_4 _$2_5)))
                                                      (=>
                                                         _$2_6
                                                         (let
                                                            ((_$2_10 (select HEAP$2_old .0$2_0_old))
                                                             (_$2_11 (select HEAP$2_old .01$2_0_old)))
                                                            (let
                                                               ((_$2_12 (+ _$2_10 _$2_11)))
                                                               (let
                                                                  ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_12)))
                                                                  (let
                                                                     ((_$2_13 (select HEAP$2 .0$2_0_old))
                                                                      (_$2_14 (select HEAP$2 .01$2_0_old)))
                                                                     (let
                                                                        ((_$2_15 (- _$2_13 _$2_14)))
                                                                        (let
                                                                           ((HEAP$2 (store HEAP$2 .01$2_0_old _$2_15)))
                                                                           (let
                                                                              ((_$2_16 (select HEAP$2 .0$2_0_old))
                                                                               (_$2_17 (select HEAP$2 .01$2_0_old)))
                                                                              (let
                                                                                 ((_$2_18 (- _$2_16 _$2_17)))
                                                                                 (let
                                                                                    ((HEAP$2 (store HEAP$2 .0$2_0_old _$2_18))
                                                                                     (_$2_19 (+ .0$2_0_old 1))
                                                                                     (_$2_20 (+ .01$2_0_old 1)))
                                                                                    (let
                                                                                       ((.01$2_0 _$2_20)
                                                                                        (.0$2_0 _$2_19)
                                                                                        (a$2_0 a$2_0_old)
                                                                                        (n$2_0 n$2_0_old))
                                                                                       (INV_42_MAIN a$1_0 b$1_0 i.0$1_0 n$1_0 .0$2_0 .01$2_0 a$2_0 n$2_0))))))))))))))))))))))))))))))
; forbidden main
; offbyn main
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
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
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ b$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9))
                               (_$1_11 i.0$1_0_old))
                              (let
                                 ((_$1_12 (+ a$1_0_old _$1_11)))
                                 (let
                                    ((HEAP$1 (store HEAP$1_old _$1_12 _$1_10))
                                     (_$1_13 i.0$1_0_old))
                                    (let
                                       ((_$1_14 (+ b$1_0_old _$1_13)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 _$1_14 _$1_7))
                                           (_$1_15 (+ i.0$1_0_old 1)))
                                          (let
                                             ((i.0$1_0 _$1_15)
                                              (a$1_0 a$1_0_old)
                                              (b$1_0 b$1_0_old)
                                              (n$1_0 n$1_0_old))
                                             (=>
                                                (and
                                                   (let
                                                      ((_$2_1 .0$2_0_old)
                                                       (_$2_2 a$2_0_old))
                                                      (let
                                                         ((_$2_3 (- _$2_1 _$2_2)))
                                                         (let
                                                            ((_$2_4 _$2_3)
                                                             (_$2_5 n$2_0_old))
                                                            (let
                                                               ((_$2_6 (< _$2_4 _$2_5)))
                                                               (=>
                                                                  _$2_6
                                                                  (let
                                                                     ((_$2_10 (select HEAP$2_old .0$2_0_old))
                                                                      (_$2_11 (select HEAP$2_old .01$2_0_old)))
                                                                     (let
                                                                        ((_$2_12 (+ _$2_10 _$2_11)))
                                                                        (let
                                                                           ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_12)))
                                                                           (let
                                                                              ((_$2_13 (select HEAP$2 .0$2_0_old))
                                                                               (_$2_14 (select HEAP$2 .01$2_0_old)))
                                                                              (let
                                                                                 ((_$2_15 (- _$2_13 _$2_14)))
                                                                                 (let
                                                                                    ((HEAP$2 (store HEAP$2 .01$2_0_old _$2_15)))
                                                                                    (let
                                                                                       ((_$2_16 (select HEAP$2 .0$2_0_old))
                                                                                        (_$2_17 (select HEAP$2 .01$2_0_old)))
                                                                                       (let
                                                                                          ((_$2_18 (- _$2_16 _$2_17)))
                                                                                          (let
                                                                                             ((HEAP$2 (store HEAP$2 .0$2_0_old _$2_18))
                                                                                              (_$2_19 (+ .0$2_0_old 1))
                                                                                              (_$2_20 (+ .01$2_0_old 1)))
                                                                                             (let
                                                                                                ((.01$2_0 _$2_20)
                                                                                                 (.0$2_0 _$2_19)
                                                                                                 (a$2_0 a$2_0_old)
                                                                                                 (n$2_0 n$2_0_old))
                                                                                                false))))))))))))))))
                                                (INV_42_MAIN a$1_0 b$1_0 i.0$1_0 n$1_0 .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_MAIN a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
         (let
            ((_$2_1 .0$2_0_old)
             (_$2_2 a$2_0_old))
            (let
               ((_$2_3 (- _$2_1 _$2_2)))
               (let
                  ((_$2_4 _$2_3)
                   (_$2_5 n$2_0_old))
                  (let
                     ((_$2_6 (< _$2_4 _$2_5)))
                     (=>
                        _$2_6
                        (let
                           ((_$2_10 (select HEAP$2_old .0$2_0_old))
                            (_$2_11 (select HEAP$2_old .01$2_0_old)))
                           (let
                              ((_$2_12 (+ _$2_10 _$2_11)))
                              (let
                                 ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_12)))
                                 (let
                                    ((_$2_13 (select HEAP$2 .0$2_0_old))
                                     (_$2_14 (select HEAP$2 .01$2_0_old)))
                                    (let
                                       ((_$2_15 (- _$2_13 _$2_14)))
                                       (let
                                          ((HEAP$2 (store HEAP$2 .01$2_0_old _$2_15)))
                                          (let
                                             ((_$2_16 (select HEAP$2 .0$2_0_old))
                                              (_$2_17 (select HEAP$2 .01$2_0_old)))
                                             (let
                                                ((_$2_18 (- _$2_16 _$2_17)))
                                                (let
                                                   ((HEAP$2 (store HEAP$2 .0$2_0_old _$2_18))
                                                    (_$2_19 (+ .0$2_0_old 1))
                                                    (_$2_20 (+ .01$2_0_old 1)))
                                                   (let
                                                      ((.01$2_0 _$2_20)
                                                       (.0$2_0 _$2_19)
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
                                                                            (_$1_8 i.0$1_0_old))
                                                                           (let
                                                                              ((_$1_9 (+ b$1_0_old _$1_8)))
                                                                              (let
                                                                                 ((_$1_10 (select HEAP$1_old _$1_9))
                                                                                  (_$1_11 i.0$1_0_old))
                                                                                 (let
                                                                                    ((_$1_12 (+ a$1_0_old _$1_11)))
                                                                                    (let
                                                                                       ((HEAP$1 (store HEAP$1_old _$1_12 _$1_10))
                                                                                        (_$1_13 i.0$1_0_old))
                                                                                       (let
                                                                                          ((_$1_14 (+ b$1_0_old _$1_13)))
                                                                                          (let
                                                                                             ((HEAP$1 (store HEAP$1 _$1_14 _$1_7))
                                                                                              (_$1_15 (+ i.0$1_0_old 1)))
                                                                                             (let
                                                                                                ((i.0$1_0 _$1_15)
                                                                                                 (a$1_0 a$1_0_old)
                                                                                                 (b$1_0 b$1_0_old)
                                                                                                 (n$1_0 n$1_0_old))
                                                                                                false)))))))))))))
                                                         (INV_42_MAIN a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0 .01$2_0 a$2_0 n$2_0))))))))))))))))))))
; end
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (n$1_0_old Int)
       (a$2_0_old Int)
       (b$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_swap_PRE a$1_0_old b$1_0_old n$1_0_old a$2_0_old b$2_0_old n$2_0_old)
         (let
            ((i.0$1_0 0)
             (a$1_0 a$1_0_old)
             (b$1_0 b$1_0_old)
             (n$1_0 n$1_0_old)
             (.01$2_0 b$2_0_old)
             (.0$2_0 a$2_0_old)
             (a$2_0 a$2_0_old)
             (n$2_0 n$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_42_PRE a$1_0 b$1_0 i.0$1_0 n$1_0 .0$2_0 .01$2_0 a$2_0 n$2_0)
                  (=>
                     (INV_42 a$1_0 b$1_0 i.0$1_0 n$1_0 .0$2_0 .01$2_0 a$2_0 n$2_0 result$1 result$2)
                     (INV_REC_swap a$1_0_old b$1_0_old n$1_0_old a$2_0_old b$2_0_old n$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 0)
                   (_$2_1 .0$2_0_old)
                   (_$2_2 a$2_0_old))
                  (let
                     ((_$2_3 (- _$2_1 _$2_2)))
                     (let
                        ((_$2_4 _$2_3)
                         (_$2_5 n$2_0_old))
                        (let
                           ((_$2_6 (< _$2_4 _$2_5)))
                           (=>
                              (not _$2_6)
                              (let
                                 ((result$2 0))
                                 (INV_42 a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
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
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ b$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9))
                               (_$1_11 i.0$1_0_old))
                              (let
                                 ((_$1_12 (+ a$1_0_old _$1_11)))
                                 (let
                                    ((HEAP$1 (store HEAP$1_old _$1_12 _$1_10))
                                     (_$1_13 i.0$1_0_old))
                                    (let
                                       ((_$1_14 (+ b$1_0_old _$1_13)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 _$1_14 _$1_7))
                                           (_$1_15 (+ i.0$1_0_old 1)))
                                          (let
                                             ((i.0$1_0 _$1_15)
                                              (a$1_0 a$1_0_old)
                                              (b$1_0 b$1_0_old)
                                              (n$1_0 n$1_0_old)
                                              (_$2_1 .0$2_0_old)
                                              (_$2_2 a$2_0_old))
                                             (let
                                                ((_$2_3 (- _$2_1 _$2_2)))
                                                (let
                                                   ((_$2_4 _$2_3)
                                                    (_$2_5 n$2_0_old))
                                                   (let
                                                      ((_$2_6 (< _$2_4 _$2_5)))
                                                      (=>
                                                         _$2_6
                                                         (let
                                                            ((_$2_10 (select HEAP$2_old .0$2_0_old))
                                                             (_$2_11 (select HEAP$2_old .01$2_0_old)))
                                                            (let
                                                               ((_$2_12 (+ _$2_10 _$2_11)))
                                                               (let
                                                                  ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_12)))
                                                                  (let
                                                                     ((_$2_13 (select HEAP$2 .0$2_0_old))
                                                                      (_$2_14 (select HEAP$2 .01$2_0_old)))
                                                                     (let
                                                                        ((_$2_15 (- _$2_13 _$2_14)))
                                                                        (let
                                                                           ((HEAP$2 (store HEAP$2 .01$2_0_old _$2_15)))
                                                                           (let
                                                                              ((_$2_16 (select HEAP$2 .0$2_0_old))
                                                                               (_$2_17 (select HEAP$2 .01$2_0_old)))
                                                                              (let
                                                                                 ((_$2_18 (- _$2_16 _$2_17)))
                                                                                 (let
                                                                                    ((HEAP$2 (store HEAP$2 .0$2_0_old _$2_18))
                                                                                     (_$2_19 (+ .0$2_0_old 1))
                                                                                     (_$2_20 (+ .01$2_0_old 1)))
                                                                                    (let
                                                                                       ((.01$2_0 _$2_20)
                                                                                        (.0$2_0 _$2_19)
                                                                                        (a$2_0 a$2_0_old)
                                                                                        (n$2_0 n$2_0_old))
                                                                                       (forall
                                                                                          ((result$1 Int)
                                                                                           (result$2 Int))
                                                                                          (and
                                                                                             (INV_42_PRE a$1_0 b$1_0 i.0$1_0 n$1_0 .0$2_0 .01$2_0 a$2_0 n$2_0)
                                                                                             (=>
                                                                                                (INV_42 a$1_0 b$1_0 i.0$1_0 n$1_0 .0$2_0 .01$2_0 a$2_0 n$2_0 result$1 result$2)
                                                                                                (INV_42 a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_swap__1_PRE a$1_0_old b$1_0_old n$1_0_old)
         (let
            ((i.0$1_0 0)
             (a$1_0 a$1_0_old)
             (b$1_0 b$1_0_old)
             (n$1_0 n$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_42__1 a$1_0 b$1_0 i.0$1_0 n$1_0 result$1)
                  (INV_REC_swap__1 a$1_0_old b$1_0_old n$1_0_old result$1)))))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 0))
                  (INV_42__1 a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old result$1)))))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old)
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
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ b$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9))
                               (_$1_11 i.0$1_0_old))
                              (let
                                 ((_$1_12 (+ a$1_0_old _$1_11)))
                                 (let
                                    ((HEAP$1 (store HEAP$1_old _$1_12 _$1_10))
                                     (_$1_13 i.0$1_0_old))
                                    (let
                                       ((_$1_14 (+ b$1_0_old _$1_13)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 _$1_14 _$1_7))
                                           (_$1_15 (+ i.0$1_0_old 1)))
                                          (let
                                             ((i.0$1_0 _$1_15)
                                              (a$1_0 a$1_0_old)
                                              (b$1_0 b$1_0_old)
                                              (n$1_0 n$1_0_old))
                                             (forall
                                                ((result$1 Int))
                                                (=>
                                                   (INV_42__1 a$1_0 b$1_0 i.0$1_0 n$1_0 result$1)
                                                   (INV_42__1 a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old result$1))))))))))))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (b$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_swap__2_PRE a$2_0_old b$2_0_old n$2_0_old)
         (let
            ((.01$2_0 b$2_0_old)
             (.0$2_0 a$2_0_old)
             (a$2_0 a$2_0_old)
             (n$2_0 n$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_42__2 .0$2_0 .01$2_0 a$2_0 n$2_0 result$2)
                  (INV_REC_swap__2 a$2_0_old b$2_0_old n$2_0_old result$2)))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
         (let
            ((_$2_1 .0$2_0_old)
             (_$2_2 a$2_0_old))
            (let
               ((_$2_3 (- _$2_1 _$2_2)))
               (let
                  ((_$2_4 _$2_3)
                   (_$2_5 n$2_0_old))
                  (let
                     ((_$2_6 (< _$2_4 _$2_5)))
                     (=>
                        (not _$2_6)
                        (let
                           ((result$2 0))
                           (INV_42__2 .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old result$2))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
         (let
            ((_$2_1 .0$2_0_old)
             (_$2_2 a$2_0_old))
            (let
               ((_$2_3 (- _$2_1 _$2_2)))
               (let
                  ((_$2_4 _$2_3)
                   (_$2_5 n$2_0_old))
                  (let
                     ((_$2_6 (< _$2_4 _$2_5)))
                     (=>
                        _$2_6
                        (let
                           ((_$2_10 (select HEAP$2_old .0$2_0_old))
                            (_$2_11 (select HEAP$2_old .01$2_0_old)))
                           (let
                              ((_$2_12 (+ _$2_10 _$2_11)))
                              (let
                                 ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_12)))
                                 (let
                                    ((_$2_13 (select HEAP$2 .0$2_0_old))
                                     (_$2_14 (select HEAP$2 .01$2_0_old)))
                                    (let
                                       ((_$2_15 (- _$2_13 _$2_14)))
                                       (let
                                          ((HEAP$2 (store HEAP$2 .01$2_0_old _$2_15)))
                                          (let
                                             ((_$2_16 (select HEAP$2 .0$2_0_old))
                                              (_$2_17 (select HEAP$2 .01$2_0_old)))
                                             (let
                                                ((_$2_18 (- _$2_16 _$2_17)))
                                                (let
                                                   ((HEAP$2 (store HEAP$2 .0$2_0_old _$2_18))
                                                    (_$2_19 (+ .0$2_0_old 1))
                                                    (_$2_20 (+ .01$2_0_old 1)))
                                                   (let
                                                      ((.01$2_0 _$2_20)
                                                       (.0$2_0 _$2_19)
                                                       (a$2_0 a$2_0_old)
                                                       (n$2_0 n$2_0_old))
                                                      (forall
                                                         ((result$2 Int))
                                                         (=>
                                                            (INV_42__2 .0$2_0 .01$2_0 a$2_0 n$2_0 result$2)
                                                            (INV_42__2 .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old result$2)))))))))))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
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
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ b$1_0_old _$1_8)))
                           (let
                              ((_$1_10 (select HEAP$1_old _$1_9))
                               (_$1_11 i.0$1_0_old))
                              (let
                                 ((_$1_12 (+ a$1_0_old _$1_11)))
                                 (let
                                    ((HEAP$1 (store HEAP$1_old _$1_12 _$1_10))
                                     (_$1_13 i.0$1_0_old))
                                    (let
                                       ((_$1_14 (+ b$1_0_old _$1_13)))
                                       (let
                                          ((HEAP$1 (store HEAP$1 _$1_14 _$1_7))
                                           (_$1_15 (+ i.0$1_0_old 1)))
                                          (let
                                             ((i.0$1_0 _$1_15)
                                              (a$1_0 a$1_0_old)
                                              (b$1_0 b$1_0_old)
                                              (n$1_0 n$1_0_old))
                                             (=>
                                                (and
                                                   (let
                                                      ((_$2_1 .0$2_0_old)
                                                       (_$2_2 a$2_0_old))
                                                      (let
                                                         ((_$2_3 (- _$2_1 _$2_2)))
                                                         (let
                                                            ((_$2_4 _$2_3)
                                                             (_$2_5 n$2_0_old))
                                                            (let
                                                               ((_$2_6 (< _$2_4 _$2_5)))
                                                               (=>
                                                                  _$2_6
                                                                  (let
                                                                     ((_$2_10 (select HEAP$2_old .0$2_0_old))
                                                                      (_$2_11 (select HEAP$2_old .01$2_0_old)))
                                                                     (let
                                                                        ((_$2_12 (+ _$2_10 _$2_11)))
                                                                        (let
                                                                           ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_12)))
                                                                           (let
                                                                              ((_$2_13 (select HEAP$2 .0$2_0_old))
                                                                               (_$2_14 (select HEAP$2 .01$2_0_old)))
                                                                              (let
                                                                                 ((_$2_15 (- _$2_13 _$2_14)))
                                                                                 (let
                                                                                    ((HEAP$2 (store HEAP$2 .01$2_0_old _$2_15)))
                                                                                    (let
                                                                                       ((_$2_16 (select HEAP$2 .0$2_0_old))
                                                                                        (_$2_17 (select HEAP$2 .01$2_0_old)))
                                                                                       (let
                                                                                          ((_$2_18 (- _$2_16 _$2_17)))
                                                                                          (let
                                                                                             ((HEAP$2 (store HEAP$2 .0$2_0_old _$2_18))
                                                                                              (_$2_19 (+ .0$2_0_old 1))
                                                                                              (_$2_20 (+ .01$2_0_old 1)))
                                                                                             (let
                                                                                                ((.01$2_0 _$2_20)
                                                                                                 (.0$2_0 _$2_19)
                                                                                                 (a$2_0 a$2_0_old)
                                                                                                 (n$2_0 n$2_0_old))
                                                                                                false))))))))))))))))
                                                (forall
                                                   ((result$1 Int)
                                                    (result$2 Int))
                                                   (and
                                                      (INV_42_PRE a$1_0 b$1_0 i.0$1_0 n$1_0 .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
                                                      (=>
                                                         (INV_42 a$1_0 b$1_0 i.0$1_0 n$1_0 .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old result$1 result$2)
                                                         (INV_42 a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (a$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old)
         (let
            ((_$2_1 .0$2_0_old)
             (_$2_2 a$2_0_old))
            (let
               ((_$2_3 (- _$2_1 _$2_2)))
               (let
                  ((_$2_4 _$2_3)
                   (_$2_5 n$2_0_old))
                  (let
                     ((_$2_6 (< _$2_4 _$2_5)))
                     (=>
                        _$2_6
                        (let
                           ((_$2_10 (select HEAP$2_old .0$2_0_old))
                            (_$2_11 (select HEAP$2_old .01$2_0_old)))
                           (let
                              ((_$2_12 (+ _$2_10 _$2_11)))
                              (let
                                 ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_12)))
                                 (let
                                    ((_$2_13 (select HEAP$2 .0$2_0_old))
                                     (_$2_14 (select HEAP$2 .01$2_0_old)))
                                    (let
                                       ((_$2_15 (- _$2_13 _$2_14)))
                                       (let
                                          ((HEAP$2 (store HEAP$2 .01$2_0_old _$2_15)))
                                          (let
                                             ((_$2_16 (select HEAP$2 .0$2_0_old))
                                              (_$2_17 (select HEAP$2 .01$2_0_old)))
                                             (let
                                                ((_$2_18 (- _$2_16 _$2_17)))
                                                (let
                                                   ((HEAP$2 (store HEAP$2 .0$2_0_old _$2_18))
                                                    (_$2_19 (+ .0$2_0_old 1))
                                                    (_$2_20 (+ .01$2_0_old 1)))
                                                   (let
                                                      ((.01$2_0 _$2_20)
                                                       (.0$2_0 _$2_19)
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
                                                                            (_$1_8 i.0$1_0_old))
                                                                           (let
                                                                              ((_$1_9 (+ b$1_0_old _$1_8)))
                                                                              (let
                                                                                 ((_$1_10 (select HEAP$1_old _$1_9))
                                                                                  (_$1_11 i.0$1_0_old))
                                                                                 (let
                                                                                    ((_$1_12 (+ a$1_0_old _$1_11)))
                                                                                    (let
                                                                                       ((HEAP$1 (store HEAP$1_old _$1_12 _$1_10))
                                                                                        (_$1_13 i.0$1_0_old))
                                                                                       (let
                                                                                          ((_$1_14 (+ b$1_0_old _$1_13)))
                                                                                          (let
                                                                                             ((HEAP$1 (store HEAP$1 _$1_14 _$1_7))
                                                                                              (_$1_15 (+ i.0$1_0_old 1)))
                                                                                             (let
                                                                                                ((i.0$1_0 _$1_15)
                                                                                                 (a$1_0 a$1_0_old)
                                                                                                 (b$1_0 b$1_0_old)
                                                                                                 (n$1_0 n$1_0_old))
                                                                                                false)))))))))))))
                                                         (forall
                                                            ((result$1 Int)
                                                             (result$2 Int))
                                                            (and
                                                               (INV_42_PRE a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0 .01$2_0 a$2_0 n$2_0)
                                                               (=>
                                                                  (INV_42 a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0 .01$2_0 a$2_0 n$2_0 result$1 result$2)
                                                                  (INV_42 a$1_0_old b$1_0_old i.0$1_0_old n$1_0_old .0$2_0_old .01$2_0_old a$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))
(check-sat)
(get-model)
