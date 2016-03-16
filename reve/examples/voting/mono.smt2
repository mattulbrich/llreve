(set-logic HORN)
(define-fun
   IN_INV
   ((res$1_0 Int)
    (C$1_0 Int)
    (HEAP$1 (Array Int Int))
    (res$2_0 Int)
    (C$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= res$1_0 res$2_0)
      (= C$1_0 C$2_0)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))
      (> C$1_0 1)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (=> (= result$1 1) (= result$2 1)))
(define-fun INV_MAIN_0
  ((C$1 Int)
   (elect$1 Int)
   (i$1 Int)
   (max$1 Int)
   (res$1 Int)
   (i1 Int)
   (heap1 Int)
   (C$2 Int)
   (elect$2 Int)
   (i$2 Int)
   (max$2 Int)
   (res$2 Int)
   (i2 Int)
   (heap2 Int))
  Bool
  (and (= C$1 C$2)
       (=> (= elect$1 1) (and (= elect$2 1) (>= max$2 max$1)))
       (<= 0 elect$2)
       (< elect$2 i$2)
       (=> (<= i$1 1) (>= max$1 max$2))
       (= i$1 i$2)
       (= res$1 res$2)
       (=> (= i1 i2) (and (=> (= i2 (+ res$2 4))
                              (>= heap2 heap1))
                          (=> (not (= i2 (+ res$2 4)))
                              (>= heap1 heap2))))))
(assert
   (forall
      ((res$1_0_old Int)
       (C$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (res$2_0_old Int)
       (C$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV res$1_0_old C$1_0_old HEAP$1_old res$2_0_old C$2_0_old HEAP$2_old)
         (let
            ((res$1_0 res$1_0_old)
             (C$1_0 C$1_0_old)
             (HEAP$1 HEAP$1_old)
             (max.0$1_0 0)
             (elect.0$1_0 0)
             (i.0$1_0 1)
             (res$2_0 res$2_0_old))
            (let
               ((C$2_0 C$2_0_old)
                (HEAP$2 HEAP$2_old)
                (_$2_0 (+ res$2_0 (* 4 1))))
               (let
                  ((_$2_1 (select HEAP$2 _$2_0)))
                  (let
                     ((_$2_2 (+ _$2_1 1)))
                     (let
                        ((HEAP$2 (store HEAP$2 _$2_0 _$2_2))
                         (max.0$2_0 0)
                         (elect.0$2_0 0)
                         (i.0$2_0 1))
                        (forall
                           ((i1 Int)
                            (i2 Int))
                           (INV_MAIN_0 C$1_0 elect.0$1_0 i.0$1_0 max.0$1_0 res$1_0 i1 (select HEAP$1 i1) C$2_0 elect.0$2_0 i.0$2_0 max.0$2_0 res$2_0 i2 (select HEAP$2 i2)))))))))))
(assert
   (forall
      ((C$1_0_old Int)
       (elect.0$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (res$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (C$2_0_old Int)
       (elect.0$2_0_old Int)
       (i.0$2_0_old Int)
       (max.0$2_0_old Int)
       (res$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 C$1_0_old elect.0$1_0_old i.0$1_0_old max.0$1_0_old res$1_0_old i1_old (select HEAP$1_old i1_old) C$2_0_old elect.0$2_0_old i.0$2_0_old max.0$2_0_old res$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((C$1_0 C$1_0_old)
             (elect.0$1_0 elect.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((max.0$1_0 max.0$1_0_old)
                (res$1_0 res$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (<= i.0$1_0 C$1_0)))
               (=>
                  (not _$1_1)
                  (let
                     ((result$1 elect.0$1_0)
                      (HEAP$1_res HEAP$1)
                      (C$2_0 C$2_0_old)
                      (elect.0$2_0 elect.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old))
                     (let
                        ((max.0$2_0 max.0$2_0_old)
                         (res$2_0 res$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (_$2_4 (<= i.0$2_0 C$2_0)))
                        (=>
                           (not _$2_4)
                           (let
                              ((result$2 elect.0$2_0)
                               (HEAP$2_res HEAP$2))
                              (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))
(assert
   (forall
      ((C$1_0_old Int)
       (elect.0$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (res$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (C$2_0_old Int)
       (elect.0$2_0_old Int)
       (i.0$2_0_old Int)
       (max.0$2_0_old Int)
       (res$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 C$1_0_old elect.0$1_0_old i.0$1_0_old max.0$1_0_old res$1_0_old i1_old (select HEAP$1_old i1_old) C$2_0_old elect.0$2_0_old i.0$2_0_old max.0$2_0_old res$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((C$1_0 C$1_0_old)
             (elect.0$1_0 elect.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((max.0$1_0 max.0$1_0_old)
                (res$1_0 res$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (<= i.0$1_0 C$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 i.0$1_0))
                     (let
                        ((_$1_3 (+ res$1_0 (* 4 _$1_2))))
                        (let
                           ((_$1_4 (select HEAP$1 _$1_3)))
                           (let
                              ((_$1_5 (< max.0$1_0 _$1_4))
                               (_$1_6 i.0$1_0))
                              (let
                                 ((_$1_7 (+ res$1_0 (* 4 _$1_6))))
                                 (let
                                    ((_$1_8 (select HEAP$1 _$1_7)))
                                    (let
                                       ((_$1_9 (= max.0$1_0 _$1_8)))
                                       (let
                                          ((.elect.0$1_0 (ite _$1_9 0 elect.0$1_0)))
                                          (let
                                             ((max.1$1_0 (ite _$1_5 _$1_8 max.0$1_0))
                                              (elect.2$1_0 (ite _$1_5 i.0$1_0 .elect.0$1_0))
                                              (_$1_10 (+ i.0$1_0 1)))
                                             (let
                                                ((max.0$1_0 max.1$1_0)
                                                 (elect.0$1_0 elect.2$1_0)
                                                 (i.0$1_0 _$1_10)
                                                 (C$2_0 C$2_0_old)
                                                 (elect.0$2_0 elect.0$2_0_old)
                                                 (i.0$2_0 i.0$2_0_old))
                                                (let
                                                   ((max.0$2_0 max.0$2_0_old)
                                                    (res$2_0 res$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (_$2_4 (<= i.0$2_0 C$2_0)))
                                                   (=>
                                                      _$2_4
                                                      (let
                                                         ((_$2_5 i.0$2_0))
                                                         (let
                                                            ((_$2_6 (+ res$2_0 (* 4 _$2_5))))
                                                            (let
                                                               ((_$2_7 (select HEAP$2 _$2_6)))
                                                               (let
                                                                  ((_$2_8 (< max.0$2_0 _$2_7))
                                                                   (_$2_9 i.0$2_0))
                                                                  (let
                                                                     ((_$2_10 (+ res$2_0 (* 4 _$2_9))))
                                                                     (let
                                                                        ((_$2_11 (select HEAP$2 _$2_10)))
                                                                        (let
                                                                           ((_$2_12 (= max.0$2_0 _$2_11)))
                                                                           (let
                                                                              ((.elect.0$2_0 (ite _$2_12 0 elect.0$2_0)))
                                                                              (let
                                                                                 ((max.1$2_0 (ite _$2_8 _$2_11 max.0$2_0))
                                                                                  (elect.2$2_0 (ite _$2_8 i.0$2_0 .elect.0$2_0))
                                                                                  (_$2_13 (+ i.0$2_0 1)))
                                                                                 (let
                                                                                    ((max.0$2_0 max.1$2_0)
                                                                                     (elect.0$2_0 elect.2$2_0)
                                                                                     (i.0$2_0 _$2_13))
                                                                                    (forall
                                                                                       ((i1 Int)
                                                                                        (i2 Int))
                                                                                       (INV_MAIN_0 C$1_0 elect.0$1_0 i.0$1_0 max.0$1_0 res$1_0 i1 (select HEAP$1 i1) C$2_0 elect.0$2_0 i.0$2_0 max.0$2_0 res$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((C$1_0_old Int)
       (elect.0$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (res$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (C$2_0_old Int)
       (elect.0$2_0_old Int)
       (i.0$2_0_old Int)
       (max.0$2_0_old Int)
       (res$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 C$1_0_old elect.0$1_0_old i.0$1_0_old max.0$1_0_old res$1_0_old i1_old (select HEAP$1_old i1_old) C$2_0_old elect.0$2_0_old i.0$2_0_old max.0$2_0_old res$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((C$1_0 C$1_0_old)
             (elect.0$1_0 elect.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((max.0$1_0 max.0$1_0_old)
                (res$1_0 res$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (<= i.0$1_0 C$1_0)))
               (=>
                  (not _$1_1)
                  (let
                     ((result$1 elect.0$1_0)
                      (HEAP$1_res HEAP$1)
                      (C$2_0 C$2_0_old)
                      (elect.0$2_0 elect.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old))
                     (let
                        ((max.0$2_0 max.0$2_0_old)
                         (res$2_0 res$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (_$2_4 (<= i.0$2_0 C$2_0)))
                        (=>
                           _$2_4
                           (let
                              ((_$2_5 i.0$2_0))
                              (let
                                 ((_$2_6 (+ res$2_0 (* 4 _$2_5))))
                                 (let
                                    ((_$2_7 (select HEAP$2 _$2_6)))
                                    (let
                                       ((_$2_8 (< max.0$2_0 _$2_7))
                                        (_$2_9 i.0$2_0))
                                       (let
                                          ((_$2_10 (+ res$2_0 (* 4 _$2_9))))
                                          (let
                                             ((_$2_11 (select HEAP$2 _$2_10)))
                                             (let
                                                ((_$2_12 (= max.0$2_0 _$2_11)))
                                                (let
                                                   ((.elect.0$2_0 (ite _$2_12 0 elect.0$2_0)))
                                                   (let
                                                      ((max.1$2_0 (ite _$2_8 _$2_11 max.0$2_0))
                                                       (elect.2$2_0 (ite _$2_8 i.0$2_0 .elect.0$2_0))
                                                       (_$2_13 (+ i.0$2_0 1)))
                                                      (let
                                                         ((max.0$2_0 max.1$2_0)
                                                          (elect.0$2_0 elect.2$2_0)
                                                          (i.0$2_0 _$2_13))
                                                         false)))))))))))))))))))
(assert
   (forall
      ((C$1_0_old Int)
       (elect.0$1_0_old Int)
       (i.0$1_0_old Int)
       (max.0$1_0_old Int)
       (res$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (C$2_0_old Int)
       (elect.0$2_0_old Int)
       (i.0$2_0_old Int)
       (max.0$2_0_old Int)
       (res$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 C$1_0_old elect.0$1_0_old i.0$1_0_old max.0$1_0_old res$1_0_old i1_old (select HEAP$1_old i1_old) C$2_0_old elect.0$2_0_old i.0$2_0_old max.0$2_0_old res$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((C$1_0 C$1_0_old)
             (elect.0$1_0 elect.0$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((max.0$1_0 max.0$1_0_old)
                (res$1_0 res$1_0_old)
                (HEAP$1 HEAP$1_old)
                (_$1_1 (<= i.0$1_0 C$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 i.0$1_0))
                     (let
                        ((_$1_3 (+ res$1_0 (* 4 _$1_2))))
                        (let
                           ((_$1_4 (select HEAP$1 _$1_3)))
                           (let
                              ((_$1_5 (< max.0$1_0 _$1_4))
                               (_$1_6 i.0$1_0))
                              (let
                                 ((_$1_7 (+ res$1_0 (* 4 _$1_6))))
                                 (let
                                    ((_$1_8 (select HEAP$1 _$1_7)))
                                    (let
                                       ((_$1_9 (= max.0$1_0 _$1_8)))
                                       (let
                                          ((.elect.0$1_0 (ite _$1_9 0 elect.0$1_0)))
                                          (let
                                             ((max.1$1_0 (ite _$1_5 _$1_8 max.0$1_0))
                                              (elect.2$1_0 (ite _$1_5 i.0$1_0 .elect.0$1_0))
                                              (_$1_10 (+ i.0$1_0 1)))
                                             (let
                                                ((max.0$1_0 max.1$1_0)
                                                 (elect.0$1_0 elect.2$1_0)
                                                 (i.0$1_0 _$1_10)
                                                 (C$2_0 C$2_0_old)
                                                 (elect.0$2_0 elect.0$2_0_old)
                                                 (i.0$2_0 i.0$2_0_old))
                                                (let
                                                   ((max.0$2_0 max.0$2_0_old)
                                                    (res$2_0 res$2_0_old)
                                                    (HEAP$2 HEAP$2_old)
                                                    (_$2_4 (<= i.0$2_0 C$2_0)))
                                                   (=>
                                                      (not _$2_4)
                                                      (let
                                                         ((result$2 elect.0$2_0)
                                                          (HEAP$2_res HEAP$2))
                                                         false)))))))))))))))))))
(check-sat)
(get-model)
