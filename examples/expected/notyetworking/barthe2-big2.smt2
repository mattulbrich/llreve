(set-logic HORN)
(define-fun
   IN_INV
   ((n$1_0 Int)
    (n$2_0 Int))
   Bool
   (and
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
    Int)
   Bool)
(declare-fun
   INV_3_MAIN
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1_PRE
   (Int)
   Bool)
(declare-fun
   INV_REC_f__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2_PRE
   (Int)
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
    Int)
   Bool)
(declare-fun
   INV_2_PRE
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_3
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
   INV_3_PRE
   (Int
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
    Int)
   Bool)
(declare-fun
   INV_2__1_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_3__1
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_3__1_PRE
   (Int
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
    Int)
   Bool)
(declare-fun
   INV_2__2_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_3__2
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_3__2_PRE
   (Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            n$1_0_old
            n$2_0_old)
         (let
            ((i.0$1_0 1)
             (x.0$1_0 1)
             (n$1_0 n$1_0_old)
             (i.0$2_0 1)
             (x.0$2_0 1)
             (n$2_0 n$2_0_old))
            (INV_1_MAIN i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (* x.0$1_0_old 1))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (x.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old)
                      (_$2_1 (<= i.0$2_0_old n$2_0_old)))
                     (=>
                        _$2_1
                        (let
                           ((_$2_5 (* x.0$2_0_old 1))
                            (_$2_6 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_6)
                               (x.0$2_0 _$2_5)
                               (n$2_0 n$2_0_old))
                              (INV_1_MAIN i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((i.1$1_0 0)
                   (x.1$1_0 x.0$1_0_old)
                   (n$1_0 n$1_0_old)
                   (_$2_1 (<= i.0$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_1)
                     (let
                        ((i.1$2_0 1)
                         (x.1$2_0 x.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (INV_2_MAIN i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0)))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
            (=>
               _$1_8
               (let
                  ((_$1_12 (+ x.1$1_0_old i.1$1_0_old))
                   (_$1_13 (+ i.1$1_0_old 1)))
                  (let
                     ((i.1$1_0 _$1_13)
                      (x.1$1_0 _$1_12)
                      (n$1_0 n$1_0_old)
                      (_$2_8 (<= i.1$2_0_old n$2_0_old)))
                     (=>
                        _$2_8
                        (let
                           ((_$2_12 (+ x.1$2_0_old i.1$2_0_old))
                            (_$2_13 (+ i.1$2_0_old 1)))
                           (let
                              ((i.1$2_0 _$2_13)
                               (x.1$2_0 _$2_12)
                               (n$2_0 n$2_0_old))
                              (INV_2_MAIN i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0)))))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
            (=>
               (not _$1_8)
               (let
                  ((i.2$1_0 1)
                   (x.2$1_0 x.1$1_0_old)
                   (n$1_0 n$1_0_old)
                   (_$2_8 (<= i.1$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_8)
                     (let
                        ((i.2$2_0 1)
                         (x.2$2_0 x.1$2_0_old)
                         (n$2_0 n$2_0_old))
                        (INV_3_MAIN i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3_MAIN i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
            (=>
               (not _$1_15)
               (let
                  ((result$1 x.2$1_0_old)
                   (_$2_15 (<= i.2$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_15)
                     (let
                        ((result$2 x.2$2_0_old))
                        (OUT_INV
                           result$1
                           result$2)))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3_MAIN i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
            (=>
               _$1_15
               (let
                  ((_$1_19 (* x.2$1_0_old 2))
                   (_$1_20 (+ i.2$1_0_old 1)))
                  (let
                     ((i.2$1_0 _$1_20)
                      (x.2$1_0 _$1_19)
                      (n$1_0 n$1_0_old)
                      (_$2_15 (<= i.2$2_0_old n$2_0_old)))
                     (=>
                        _$2_15
                        (let
                           ((_$2_19 (* x.2$2_0_old 2))
                            (_$2_20 (+ i.2$2_0_old 1)))
                           (let
                              ((i.2$2_0 _$2_20)
                               (x.2$2_0 _$2_19)
                               (n$2_0 n$2_0_old))
                              (INV_3_MAIN i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)))))))))))
; forbidden main
; offbyn main
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (* x.0$1_0_old 1))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (x.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_1 (<= i.0$2_0_old n$2_0_old)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_5 (* x.0$2_0_old 1))
                                     (_$2_6 (+ i.0$2_0_old 1)))
                                    (let
                                       ((i.0$2_0 _$2_6)
                                        (x.0$2_0 _$2_5)
                                        (n$2_0 n$2_0_old))
                                       false)))))
                        (INV_1_MAIN i.0$1_0 n$1_0 x.0$1_0 i.0$2_0_old n$2_0_old x.0$2_0_old)))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
            (=>
               _$1_8
               (let
                  ((_$1_12 (+ x.1$1_0_old i.1$1_0_old))
                   (_$1_13 (+ i.1$1_0_old 1)))
                  (let
                     ((i.1$1_0 _$1_13)
                      (x.1$1_0 _$1_12)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_8 (<= i.1$2_0_old n$2_0_old)))
                              (=>
                                 _$2_8
                                 (let
                                    ((_$2_12 (+ x.1$2_0_old i.1$2_0_old))
                                     (_$2_13 (+ i.1$2_0_old 1)))
                                    (let
                                       ((i.1$2_0 _$2_13)
                                        (x.1$2_0 _$2_12)
                                        (n$2_0 n$2_0_old))
                                       false)))))
                        (INV_2_MAIN i.1$1_0 n$1_0 x.1$1_0 i.1$2_0_old n$2_0_old x.1$2_0_old)))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3_MAIN i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
            (=>
               _$1_15
               (let
                  ((_$1_19 (* x.2$1_0_old 2))
                   (_$1_20 (+ i.2$1_0_old 1)))
                  (let
                     ((i.2$1_0 _$1_20)
                      (x.2$1_0 _$1_19)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_15 (<= i.2$2_0_old n$2_0_old)))
                              (=>
                                 _$2_15
                                 (let
                                    ((_$2_19 (* x.2$2_0_old 2))
                                     (_$2_20 (+ i.2$2_0_old 1)))
                                    (let
                                       ((i.2$2_0 _$2_20)
                                        (x.2$2_0 _$2_19)
                                        (n$2_0 n$2_0_old))
                                       false)))))
                        (INV_3_MAIN i.2$1_0 n$1_0 x.2$1_0 i.2$2_0_old n$2_0_old x.2$2_0_old)))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old n$2_0_old)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (* x.0$2_0_old 1))
                   (_$2_6 (+ i.0$2_0_old 1)))
                  (let
                     ((i.0$2_0 _$2_6)
                      (x.0$2_0 _$2_5)
                      (n$2_0 n$2_0_old))
                     (=>
                        (and
                           (let
                              ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
                              (=>
                                 _$1_1
                                 (let
                                    ((_$1_5 (* x.0$1_0_old 1))
                                     (_$1_6 (+ i.0$1_0_old 1)))
                                    (let
                                       ((i.0$1_0 _$1_6)
                                        (x.0$1_0 _$1_5)
                                        (n$1_0 n$1_0_old))
                                       false)))))
                        (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0 n$2_0 x.0$2_0)))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$2_8 (<= i.1$2_0_old n$2_0_old)))
            (=>
               _$2_8
               (let
                  ((_$2_12 (+ x.1$2_0_old i.1$2_0_old))
                   (_$2_13 (+ i.1$2_0_old 1)))
                  (let
                     ((i.1$2_0 _$2_13)
                      (x.1$2_0 _$2_12)
                      (n$2_0 n$2_0_old))
                     (=>
                        (and
                           (let
                              ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
                              (=>
                                 _$1_8
                                 (let
                                    ((_$1_12 (+ x.1$1_0_old i.1$1_0_old))
                                     (_$1_13 (+ i.1$1_0_old 1)))
                                    (let
                                       ((i.1$1_0 _$1_13)
                                        (x.1$1_0 _$1_12)
                                        (n$1_0 n$1_0_old))
                                       false)))))
                        (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0 n$2_0 x.1$2_0)))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3_MAIN i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$2_15 (<= i.2$2_0_old n$2_0_old)))
            (=>
               _$2_15
               (let
                  ((_$2_19 (* x.2$2_0_old 2))
                   (_$2_20 (+ i.2$2_0_old 1)))
                  (let
                     ((i.2$2_0 _$2_20)
                      (x.2$2_0 _$2_19)
                      (n$2_0 n$2_0_old))
                     (=>
                        (and
                           (let
                              ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
                              (=>
                                 _$1_15
                                 (let
                                    ((_$1_19 (* x.2$1_0_old 2))
                                     (_$1_20 (+ i.2$1_0_old 1)))
                                    (let
                                       ((i.2$1_0 _$1_20)
                                        (x.2$1_0 _$1_19)
                                        (n$1_0 n$1_0_old))
                                       false)))))
                        (INV_3_MAIN i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0 n$2_0 x.2$2_0)))))))))
; end
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old)
         (let
            ((i.0$1_0 1)
             (x.0$1_0 1)
             (n$1_0 n$1_0_old)
             (i.0$2_0 1)
             (x.0$2_0 1)
             (n$2_0 n$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_1_PRE i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)
                  (=>
                     (INV_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0 result$1 result$2)
                     (INV_REC_f n$1_0_old n$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_PRE i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (* x.0$1_0_old 1))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (x.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old)
                      (_$2_1 (<= i.0$2_0_old n$2_0_old)))
                     (=>
                        _$2_1
                        (let
                           ((_$2_5 (* x.0$2_0_old 1))
                            (_$2_6 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_6)
                               (x.0$2_0 _$2_5)
                               (n$2_0 n$2_0_old))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_1_PRE i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)
                                    (=>
                                       (INV_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0 result$1 result$2)
                                       (INV_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_PRE i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((i.1$1_0 0)
                   (x.1$1_0 x.0$1_0_old)
                   (n$1_0 n$1_0_old)
                   (_$2_1 (<= i.0$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_1)
                     (let
                        ((i.1$2_0 1)
                         (x.1$2_0 x.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_2_PRE i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0)
                              (=>
                                 (INV_2 i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0 result$1 result$2)
                                 (INV_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2_PRE i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
            (=>
               _$1_8
               (let
                  ((_$1_12 (+ x.1$1_0_old i.1$1_0_old))
                   (_$1_13 (+ i.1$1_0_old 1)))
                  (let
                     ((i.1$1_0 _$1_13)
                      (x.1$1_0 _$1_12)
                      (n$1_0 n$1_0_old)
                      (_$2_8 (<= i.1$2_0_old n$2_0_old)))
                     (=>
                        _$2_8
                        (let
                           ((_$2_12 (+ x.1$2_0_old i.1$2_0_old))
                            (_$2_13 (+ i.1$2_0_old 1)))
                           (let
                              ((i.1$2_0 _$2_13)
                               (x.1$2_0 _$2_12)
                               (n$2_0 n$2_0_old))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_2_PRE i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0)
                                    (=>
                                       (INV_2 i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0 result$1 result$2)
                                       (INV_2 i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2_PRE i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
            (=>
               (not _$1_8)
               (let
                  ((i.2$1_0 1)
                   (x.2$1_0 x.1$1_0_old)
                   (n$1_0 n$1_0_old)
                   (_$2_8 (<= i.1$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_8)
                     (let
                        ((i.2$2_0 1)
                         (x.2$2_0 x.1$2_0_old)
                         (n$2_0 n$2_0_old))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_3_PRE i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)
                              (=>
                                 (INV_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0 result$1 result$2)
                                 (INV_2 i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3_PRE i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
            (=>
               (not _$1_15)
               (let
                  ((result$1 x.2$1_0_old)
                   (_$2_15 (<= i.2$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_15)
                     (let
                        ((result$2 x.2$2_0_old))
                        (INV_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old result$1 result$2)))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3_PRE i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
            (=>
               _$1_15
               (let
                  ((_$1_19 (* x.2$1_0_old 2))
                   (_$1_20 (+ i.2$1_0_old 1)))
                  (let
                     ((i.2$1_0 _$1_20)
                      (x.2$1_0 _$1_19)
                      (n$1_0 n$1_0_old)
                      (_$2_15 (<= i.2$2_0_old n$2_0_old)))
                     (=>
                        _$2_15
                        (let
                           ((_$2_19 (* x.2$2_0_old 2))
                            (_$2_20 (+ i.2$2_0_old 1)))
                           (let
                              ((i.2$2_0 _$2_20)
                               (x.2$2_0 _$2_19)
                               (n$2_0 n$2_0_old))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_3_PRE i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)
                                    (=>
                                       (INV_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0 result$1 result$2)
                                       (INV_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE n$1_0_old)
         (let
            ((i.0$1_0 1)
             (x.0$1_0 1)
             (n$1_0 n$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_1__1 i.0$1_0 n$1_0 x.0$1_0 result$1)
                  (INV_REC_f__1 n$1_0_old result$1)))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int))
      (=>
         (INV_1__1_PRE i.0$1_0_old n$1_0_old x.0$1_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (* x.0$1_0_old 1))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (x.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_1__1 i.0$1_0 n$1_0 x.0$1_0 result$1)
                           (INV_1__1 i.0$1_0_old n$1_0_old x.0$1_0_old result$1))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int))
      (=>
         (INV_1__1_PRE i.0$1_0_old n$1_0_old x.0$1_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((i.1$1_0 0)
                   (x.1$1_0 x.0$1_0_old)
                   (n$1_0 n$1_0_old))
                  (forall
                     ((result$1 Int))
                     (=>
                        (INV_2__1 i.1$1_0 n$1_0 x.1$1_0 result$1)
                        (INV_1__1 i.0$1_0_old n$1_0_old x.0$1_0_old result$1)))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int))
      (=>
         (INV_2__1_PRE i.1$1_0_old n$1_0_old x.1$1_0_old)
         (let
            ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
            (=>
               _$1_8
               (let
                  ((_$1_12 (+ x.1$1_0_old i.1$1_0_old))
                   (_$1_13 (+ i.1$1_0_old 1)))
                  (let
                     ((i.1$1_0 _$1_13)
                      (x.1$1_0 _$1_12)
                      (n$1_0 n$1_0_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_2__1 i.1$1_0 n$1_0 x.1$1_0 result$1)
                           (INV_2__1 i.1$1_0_old n$1_0_old x.1$1_0_old result$1))))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int))
      (=>
         (INV_2__1_PRE i.1$1_0_old n$1_0_old x.1$1_0_old)
         (let
            ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
            (=>
               (not _$1_8)
               (let
                  ((i.2$1_0 1)
                   (x.2$1_0 x.1$1_0_old)
                   (n$1_0 n$1_0_old))
                  (forall
                     ((result$1 Int))
                     (=>
                        (INV_3__1 i.2$1_0 n$1_0 x.2$1_0 result$1)
                        (INV_2__1 i.1$1_0_old n$1_0_old x.1$1_0_old result$1)))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int))
      (=>
         (INV_3__1_PRE i.2$1_0_old n$1_0_old x.2$1_0_old)
         (let
            ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
            (=>
               (not _$1_15)
               (let
                  ((result$1 x.2$1_0_old))
                  (INV_3__1 i.2$1_0_old n$1_0_old x.2$1_0_old result$1)))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int))
      (=>
         (INV_3__1_PRE i.2$1_0_old n$1_0_old x.2$1_0_old)
         (let
            ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
            (=>
               _$1_15
               (let
                  ((_$1_19 (* x.2$1_0_old 2))
                   (_$1_20 (+ i.2$1_0_old 1)))
                  (let
                     ((i.2$1_0 _$1_20)
                      (x.2$1_0 _$1_19)
                      (n$1_0 n$1_0_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_3__1 i.2$1_0 n$1_0 x.2$1_0 result$1)
                           (INV_3__1 i.2$1_0_old n$1_0_old x.2$1_0_old result$1))))))))))
(assert
   (forall
      ((n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE n$2_0_old)
         (let
            ((i.0$2_0 1)
             (x.0$2_0 1)
             (n$2_0 n$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_1__2 i.0$2_0 n$2_0 x.0$2_0 result$2)
                  (INV_REC_f__2 n$2_0_old result$2)))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1__2_PRE i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old n$2_0_old)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (* x.0$2_0_old 1))
                   (_$2_6 (+ i.0$2_0_old 1)))
                  (let
                     ((i.0$2_0 _$2_6)
                      (x.0$2_0 _$2_5)
                      (n$2_0 n$2_0_old))
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_1__2 i.0$2_0 n$2_0 x.0$2_0 result$2)
                           (INV_1__2 i.0$2_0_old n$2_0_old x.0$2_0_old result$2))))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1__2_PRE i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old n$2_0_old)))
            (=>
               (not _$2_1)
               (let
                  ((i.1$2_0 1)
                   (x.1$2_0 x.0$2_0_old)
                   (n$2_0 n$2_0_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_2__2 i.1$2_0 n$2_0 x.1$2_0 result$2)
                        (INV_1__2 i.0$2_0_old n$2_0_old x.0$2_0_old result$2)))))))))
(assert
   (forall
      ((i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2__2_PRE i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$2_8 (<= i.1$2_0_old n$2_0_old)))
            (=>
               _$2_8
               (let
                  ((_$2_12 (+ x.1$2_0_old i.1$2_0_old))
                   (_$2_13 (+ i.1$2_0_old 1)))
                  (let
                     ((i.1$2_0 _$2_13)
                      (x.1$2_0 _$2_12)
                      (n$2_0 n$2_0_old))
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_2__2 i.1$2_0 n$2_0 x.1$2_0 result$2)
                           (INV_2__2 i.1$2_0_old n$2_0_old x.1$2_0_old result$2))))))))))
(assert
   (forall
      ((i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2__2_PRE i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$2_8 (<= i.1$2_0_old n$2_0_old)))
            (=>
               (not _$2_8)
               (let
                  ((i.2$2_0 1)
                   (x.2$2_0 x.1$2_0_old)
                   (n$2_0 n$2_0_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_3__2 i.2$2_0 n$2_0 x.2$2_0 result$2)
                        (INV_2__2 i.1$2_0_old n$2_0_old x.1$2_0_old result$2)))))))))
(assert
   (forall
      ((i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3__2_PRE i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$2_15 (<= i.2$2_0_old n$2_0_old)))
            (=>
               (not _$2_15)
               (let
                  ((result$2 x.2$2_0_old))
                  (INV_3__2 i.2$2_0_old n$2_0_old x.2$2_0_old result$2)))))))
(assert
   (forall
      ((i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3__2_PRE i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$2_15 (<= i.2$2_0_old n$2_0_old)))
            (=>
               _$2_15
               (let
                  ((_$2_19 (* x.2$2_0_old 2))
                   (_$2_20 (+ i.2$2_0_old 1)))
                  (let
                     ((i.2$2_0 _$2_20)
                      (x.2$2_0 _$2_19)
                      (n$2_0 n$2_0_old))
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_3__2 i.2$2_0 n$2_0 x.2$2_0 result$2)
                           (INV_3__2 i.2$2_0_old n$2_0_old x.2$2_0_old result$2))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_PRE i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (* x.0$1_0_old 1))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (x.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_1 (<= i.0$2_0_old n$2_0_old)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_5 (* x.0$2_0_old 1))
                                     (_$2_6 (+ i.0$2_0_old 1)))
                                    (let
                                       ((i.0$2_0 _$2_6)
                                        (x.0$2_0 _$2_5)
                                        (n$2_0 n$2_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_1_PRE i.0$1_0 n$1_0 x.0$1_0 i.0$2_0_old n$2_0_old x.0$2_0_old)
                              (=>
                                 (INV_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0_old n$2_0_old x.0$2_0_old result$1 result$2)
                                 (INV_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2_PRE i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
            (=>
               _$1_8
               (let
                  ((_$1_12 (+ x.1$1_0_old i.1$1_0_old))
                   (_$1_13 (+ i.1$1_0_old 1)))
                  (let
                     ((i.1$1_0 _$1_13)
                      (x.1$1_0 _$1_12)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_8 (<= i.1$2_0_old n$2_0_old)))
                              (=>
                                 _$2_8
                                 (let
                                    ((_$2_12 (+ x.1$2_0_old i.1$2_0_old))
                                     (_$2_13 (+ i.1$2_0_old 1)))
                                    (let
                                       ((i.1$2_0 _$2_13)
                                        (x.1$2_0 _$2_12)
                                        (n$2_0 n$2_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_2_PRE i.1$1_0 n$1_0 x.1$1_0 i.1$2_0_old n$2_0_old x.1$2_0_old)
                              (=>
                                 (INV_2 i.1$1_0 n$1_0 x.1$1_0 i.1$2_0_old n$2_0_old x.1$2_0_old result$1 result$2)
                                 (INV_2 i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3_PRE i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
            (=>
               _$1_15
               (let
                  ((_$1_19 (* x.2$1_0_old 2))
                   (_$1_20 (+ i.2$1_0_old 1)))
                  (let
                     ((i.2$1_0 _$1_20)
                      (x.2$1_0 _$1_19)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_15 (<= i.2$2_0_old n$2_0_old)))
                              (=>
                                 _$2_15
                                 (let
                                    ((_$2_19 (* x.2$2_0_old 2))
                                     (_$2_20 (+ i.2$2_0_old 1)))
                                    (let
                                       ((i.2$2_0 _$2_20)
                                        (x.2$2_0 _$2_19)
                                        (n$2_0 n$2_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_3_PRE i.2$1_0 n$1_0 x.2$1_0 i.2$2_0_old n$2_0_old x.2$2_0_old)
                              (=>
                                 (INV_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0_old n$2_0_old x.2$2_0_old result$1 result$2)
                                 (INV_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_PRE i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old n$2_0_old)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (* x.0$2_0_old 1))
                   (_$2_6 (+ i.0$2_0_old 1)))
                  (let
                     ((i.0$2_0 _$2_6)
                      (x.0$2_0 _$2_5)
                      (n$2_0 n$2_0_old))
                     (=>
                        (and
                           (let
                              ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
                              (=>
                                 _$1_1
                                 (let
                                    ((_$1_5 (* x.0$1_0_old 1))
                                     (_$1_6 (+ i.0$1_0_old 1)))
                                    (let
                                       ((i.0$1_0 _$1_6)
                                        (x.0$1_0 _$1_5)
                                        (n$1_0 n$1_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_1_PRE i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0 n$2_0 x.0$2_0)
                              (=>
                                 (INV_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0 n$2_0 x.0$2_0 result$1 result$2)
                                 (INV_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_2_PRE i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((_$2_8 (<= i.1$2_0_old n$2_0_old)))
            (=>
               _$2_8
               (let
                  ((_$2_12 (+ x.1$2_0_old i.1$2_0_old))
                   (_$2_13 (+ i.1$2_0_old 1)))
                  (let
                     ((i.1$2_0 _$2_13)
                      (x.1$2_0 _$2_12)
                      (n$2_0 n$2_0_old))
                     (=>
                        (and
                           (let
                              ((_$1_8 (<= i.1$1_0_old n$1_0_old)))
                              (=>
                                 _$1_8
                                 (let
                                    ((_$1_12 (+ x.1$1_0_old i.1$1_0_old))
                                     (_$1_13 (+ i.1$1_0_old 1)))
                                    (let
                                       ((i.1$1_0 _$1_13)
                                        (x.1$1_0 _$1_12)
                                        (n$1_0 n$1_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_2_PRE i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0 n$2_0 x.1$2_0)
                              (=>
                                 (INV_2 i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0 n$2_0 x.1$2_0 result$1 result$2)
                                 (INV_2 i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_3_PRE i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((_$2_15 (<= i.2$2_0_old n$2_0_old)))
            (=>
               _$2_15
               (let
                  ((_$2_19 (* x.2$2_0_old 2))
                   (_$2_20 (+ i.2$2_0_old 1)))
                  (let
                     ((i.2$2_0 _$2_20)
                      (x.2$2_0 _$2_19)
                      (n$2_0 n$2_0_old))
                     (=>
                        (and
                           (let
                              ((_$1_15 (<= i.2$1_0_old n$1_0_old)))
                              (=>
                                 _$1_15
                                 (let
                                    ((_$1_19 (* x.2$1_0_old 2))
                                     (_$1_20 (+ i.2$1_0_old 1)))
                                    (let
                                       ((i.2$1_0 _$1_20)
                                        (x.2$1_0 _$1_19)
                                        (n$1_0 n$1_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_3_PRE i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0 n$2_0 x.2$2_0)
                              (=>
                                 (INV_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0 n$2_0 x.2$2_0 result$1 result$2)
                                 (INV_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old result$1 result$2))))))))))))
(check-sat)
(get-model)
