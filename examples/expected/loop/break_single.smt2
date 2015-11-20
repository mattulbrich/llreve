(set-logic HORN)
(define-fun
   IN_INV
   ((x$1_0 Int)
    (x$2_0 Int))
   Bool
   (and
      (= x$1_0 x$2_0)))
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
   INV_42
   (Int
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
    Int)
   Bool)
(declare-fun
   INV_42__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_42__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__2_PRE
   (Int
    Int)
   Bool)
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (IN_INV
            x$1_0_old
            x$2_0_old)
         (let
            ((i.0$1_0 0)
             (x$1_0 x$1_0_old)
             (i.0$2_0 0)
             (x$2_0 x$2_0_old))
            (INV_42_MAIN i.0$1_0 x$1_0 i.0$2_0 x$2_0)))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     _$1_5
                     (let
                        ((result$1 i.0$1_0_old)
                         (_$2_1 (<= i.0$2_0_old 10)))
                        (=>
                           _$2_1
                           (let
                              ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                              (let
                                 ((_$2_3 _$2_2))
                                 (=>
                                    (not _$2_3)
                                    (let
                                       ((result$2 i.0$2_0_old))
                                       (OUT_INV
                                          result$1
                                          result$2))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     _$1_5
                     (let
                        ((result$1 i.0$1_0_old)
                         (_$2_1 (<= i.0$2_0_old 10)))
                        (=>
                           (not _$2_1)
                           (let
                              ((_$2_3 false))
                              (=>
                                 (not _$2_3)
                                 (let
                                    ((result$2 i.0$2_0_old))
                                    (OUT_INV
                                       result$1
                                       result$2)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 i.0$1_0_old)
                   (_$2_1 (<= i.0$2_0_old 10)))
                  (=>
                     _$2_1
                     (let
                        ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                        (let
                           ((_$2_3 _$2_2))
                           (=>
                              (not _$2_3)
                              (let
                                 ((result$2 i.0$2_0_old))
                                 (OUT_INV
                                    result$1
                                    result$2))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 i.0$1_0_old)
                   (_$2_1 (<= i.0$2_0_old 10)))
                  (=>
                     (not _$2_1)
                     (let
                        ((_$2_3 false))
                        (=>
                           (not _$2_3)
                           (let
                              ((result$2 i.0$2_0_old))
                              (OUT_INV
                                 result$1
                                 result$2)))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     (not _$1_5)
                     (let
                        ((_$1_6 (+ i.0$1_0_old 1)))
                        (let
                           ((i.0$1_0 _$1_6)
                            (x$1_0 x$1_0_old)
                            (_$2_1 (<= i.0$2_0_old 10)))
                           (=>
                              _$2_1
                              (let
                                 ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                                 (let
                                    ((_$2_3 _$2_2))
                                    (=>
                                       _$2_3
                                       (let
                                          ((_$2_7 (+ i.0$2_0_old 1)))
                                          (let
                                             ((i.0$2_0 _$2_7)
                                              (x$2_0 x$2_0_old))
                                             (INV_42_MAIN i.0$1_0 x$1_0 i.0$2_0 x$2_0))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     (not _$1_5)
                     (let
                        ((_$1_6 (+ i.0$1_0_old 1)))
                        (let
                           ((i.0$1_0 _$1_6)
                            (x$1_0 x$1_0_old)
                            (_$2_1 (<= i.0$2_0_old 10)))
                           (=>
                              (not _$2_1)
                              (let
                                 ((_$2_3 false))
                                 (=>
                                    _$2_3
                                    (let
                                       ((_$2_7 (+ i.0$2_0_old 1)))
                                       (let
                                          ((i.0$2_0 _$2_7)
                                           (x$2_0 x$2_0_old))
                                          (INV_42_MAIN i.0$1_0 x$1_0 i.0$2_0 x$2_0)))))))))))))))
; forbidden main
; offbyn main
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     (not _$1_5)
                     (let
                        ((_$1_6 (+ i.0$1_0_old 1)))
                        (let
                           ((i.0$1_0 _$1_6)
                            (x$1_0 x$1_0_old))
                           (=>
                              (and
                                 (let
                                    ((_$2_1 (<= i.0$2_0_old 10)))
                                    (=>
                                       _$2_1
                                       (let
                                          ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                                          (let
                                             ((_$2_3 _$2_2))
                                             (=>
                                                _$2_3
                                                (let
                                                   ((_$2_7 (+ i.0$2_0_old 1)))
                                                   (let
                                                      ((i.0$2_0 _$2_7)
                                                       (x$2_0 x$2_0_old))
                                                      false)))))))
                                 (let
                                    ((_$2_1 (<= i.0$2_0_old 10)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_3 false))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 (+ i.0$2_0_old 1)))
                                                (let
                                                   ((i.0$2_0 _$2_7)
                                                    (x$2_0 x$2_0_old))
                                                   false)))))))
                              (INV_42_MAIN i.0$1_0 x$1_0 i.0$2_0_old x$2_0_old)))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old 10)))
            (=>
               _$2_1
               (let
                  ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                  (let
                     ((_$2_3 _$2_2))
                     (=>
                        _$2_3
                        (let
                           ((_$2_7 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_7)
                               (x$2_0 x$2_0_old))
                              (=>
                                 (and
                                    (let
                                       ((_$1_1 (<= i.0$1_0_old 10)))
                                       (=>
                                          _$1_1
                                          (let
                                             ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                                             (=>
                                                (not _$1_5)
                                                (let
                                                   ((_$1_6 (+ i.0$1_0_old 1)))
                                                   (let
                                                      ((i.0$1_0 _$1_6)
                                                       (x$1_0 x$1_0_old))
                                                      false)))))))
                                 (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0 x$2_0))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old 10)))
            (=>
               (not _$2_1)
               (let
                  ((_$2_3 false))
                  (=>
                     _$2_3
                     (let
                        ((_$2_7 (+ i.0$2_0_old 1)))
                        (let
                           ((i.0$2_0 _$2_7)
                            (x$2_0 x$2_0_old))
                           (=>
                              (and
                                 (let
                                    ((_$1_1 (<= i.0$1_0_old 10)))
                                    (=>
                                       _$1_1
                                       (let
                                          ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                                          (=>
                                             (not _$1_5)
                                             (let
                                                ((_$1_6 (+ i.0$1_0_old 1)))
                                                (let
                                                   ((i.0$1_0 _$1_6)
                                                    (x$1_0 x$1_0_old))
                                                   false)))))))
                              (INV_42_MAIN i.0$1_0_old x$1_0_old i.0$2_0 x$2_0)))))))))))
; end
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((i.0$1_0 0)
             (x$1_0 x$1_0_old)
             (i.0$2_0 0)
             (x$2_0 x$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_42_PRE i.0$1_0 x$1_0 i.0$2_0 x$2_0)
                  (=>
                     (INV_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0 result$1 result$2)
                     (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     _$1_5
                     (let
                        ((result$1 i.0$1_0_old)
                         (_$2_1 (<= i.0$2_0_old 10)))
                        (=>
                           _$2_1
                           (let
                              ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                              (let
                                 ((_$2_3 _$2_2))
                                 (=>
                                    (not _$2_3)
                                    (let
                                       ((result$2 i.0$2_0_old))
                                       (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     _$1_5
                     (let
                        ((result$1 i.0$1_0_old)
                         (_$2_1 (<= i.0$2_0_old 10)))
                        (=>
                           (not _$2_1)
                           (let
                              ((_$2_3 false))
                              (=>
                                 (not _$2_3)
                                 (let
                                    ((result$2 i.0$2_0_old))
                                    (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 i.0$1_0_old)
                   (_$2_1 (<= i.0$2_0_old 10)))
                  (=>
                     _$2_1
                     (let
                        ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                        (let
                           ((_$2_3 _$2_2))
                           (=>
                              (not _$2_3)
                              (let
                                 ((result$2 i.0$2_0_old))
                                 (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 i.0$1_0_old)
                   (_$2_1 (<= i.0$2_0_old 10)))
                  (=>
                     (not _$2_1)
                     (let
                        ((_$2_3 false))
                        (=>
                           (not _$2_3)
                           (let
                              ((result$2 i.0$2_0_old))
                              (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     (not _$1_5)
                     (let
                        ((_$1_6 (+ i.0$1_0_old 1)))
                        (let
                           ((i.0$1_0 _$1_6)
                            (x$1_0 x$1_0_old)
                            (_$2_1 (<= i.0$2_0_old 10)))
                           (=>
                              _$2_1
                              (let
                                 ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                                 (let
                                    ((_$2_3 _$2_2))
                                    (=>
                                       _$2_3
                                       (let
                                          ((_$2_7 (+ i.0$2_0_old 1)))
                                          (let
                                             ((i.0$2_0 _$2_7)
                                              (x$2_0 x$2_0_old))
                                             (forall
                                                ((result$1 Int)
                                                 (result$2 Int))
                                                (and
                                                   (INV_42_PRE i.0$1_0 x$1_0 i.0$2_0 x$2_0)
                                                   (=>
                                                      (INV_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0 result$1 result$2)
                                                      (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     (not _$1_5)
                     (let
                        ((_$1_6 (+ i.0$1_0_old 1)))
                        (let
                           ((i.0$1_0 _$1_6)
                            (x$1_0 x$1_0_old)
                            (_$2_1 (<= i.0$2_0_old 10)))
                           (=>
                              (not _$2_1)
                              (let
                                 ((_$2_3 false))
                                 (=>
                                    _$2_3
                                    (let
                                       ((_$2_7 (+ i.0$2_0_old 1)))
                                       (let
                                          ((i.0$2_0 _$2_7)
                                           (x$2_0 x$2_0_old))
                                          (forall
                                             ((result$1 Int)
                                              (result$2 Int))
                                             (and
                                                (INV_42_PRE i.0$1_0 x$1_0 i.0$2_0 x$2_0)
                                                (=>
                                                   (INV_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0 result$1 result$2)
                                                   (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE x$1_0_old)
         (let
            ((i.0$1_0 0)
             (x$1_0 x$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_42__1 i.0$1_0 x$1_0 result$1)
                  (INV_REC_f__1 x$1_0_old result$1)))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int))
      (=>
         (INV_42__1_PRE i.0$1_0_old x$1_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     _$1_5
                     (let
                        ((result$1 i.0$1_0_old))
                        (INV_42__1 i.0$1_0_old x$1_0_old result$1)))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int))
      (=>
         (INV_42__1_PRE i.0$1_0_old x$1_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 i.0$1_0_old))
                  (INV_42__1 i.0$1_0_old x$1_0_old result$1)))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int))
      (=>
         (INV_42__1_PRE i.0$1_0_old x$1_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     (not _$1_5)
                     (let
                        ((_$1_6 (+ i.0$1_0_old 1)))
                        (let
                           ((i.0$1_0 _$1_6)
                            (x$1_0 x$1_0_old))
                           (forall
                              ((result$1 Int))
                              (=>
                                 (INV_42__1 i.0$1_0 x$1_0 result$1)
                                 (INV_42__1 i.0$1_0_old x$1_0_old result$1))))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old)
         (let
            ((i.0$2_0 0)
             (x$2_0 x$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_42__2 i.0$2_0 x$2_0 result$2)
                  (INV_REC_f__2 x$2_0_old result$2)))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old x$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old 10)))
            (=>
               _$2_1
               (let
                  ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                  (let
                     ((_$2_3 _$2_2))
                     (=>
                        (not _$2_3)
                        (let
                           ((result$2 i.0$2_0_old))
                           (INV_42__2 i.0$2_0_old x$2_0_old result$2))))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old x$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old 10)))
            (=>
               (not _$2_1)
               (let
                  ((_$2_3 false))
                  (=>
                     (not _$2_3)
                     (let
                        ((result$2 i.0$2_0_old))
                        (INV_42__2 i.0$2_0_old x$2_0_old result$2)))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old x$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old 10)))
            (=>
               _$2_1
               (let
                  ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                  (let
                     ((_$2_3 _$2_2))
                     (=>
                        _$2_3
                        (let
                           ((_$2_7 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_7)
                               (x$2_0 x$2_0_old))
                              (forall
                                 ((result$2 Int))
                                 (=>
                                    (INV_42__2 i.0$2_0 x$2_0 result$2)
                                    (INV_42__2 i.0$2_0_old x$2_0_old result$2)))))))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old x$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old 10)))
            (=>
               (not _$2_1)
               (let
                  ((_$2_3 false))
                  (=>
                     _$2_3
                     (let
                        ((_$2_7 (+ i.0$2_0_old 1)))
                        (let
                           ((i.0$2_0 _$2_7)
                            (x$2_0 x$2_0_old))
                           (forall
                              ((result$2 Int))
                              (=>
                                 (INV_42__2 i.0$2_0 x$2_0 result$2)
                                 (INV_42__2 i.0$2_0_old x$2_0_old result$2))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                  (=>
                     (not _$1_5)
                     (let
                        ((_$1_6 (+ i.0$1_0_old 1)))
                        (let
                           ((i.0$1_0 _$1_6)
                            (x$1_0 x$1_0_old))
                           (=>
                              (and
                                 (let
                                    ((_$2_1 (<= i.0$2_0_old 10)))
                                    (=>
                                       _$2_1
                                       (let
                                          ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                                          (let
                                             ((_$2_3 _$2_2))
                                             (=>
                                                _$2_3
                                                (let
                                                   ((_$2_7 (+ i.0$2_0_old 1)))
                                                   (let
                                                      ((i.0$2_0 _$2_7)
                                                       (x$2_0 x$2_0_old))
                                                      false)))))))
                                 (let
                                    ((_$2_1 (<= i.0$2_0_old 10)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_3 false))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_7 (+ i.0$2_0_old 1)))
                                                (let
                                                   ((i.0$2_0 _$2_7)
                                                    (x$2_0 x$2_0_old))
                                                   false)))))))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_42_PRE i.0$1_0 x$1_0 i.0$2_0_old x$2_0_old)
                                    (=>
                                       (INV_42 i.0$1_0 x$1_0 i.0$2_0_old x$2_0_old result$1 result$2)
                                       (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old 10)))
            (=>
               _$2_1
               (let
                  ((_$2_2 (distinct i.0$2_0_old x$2_0_old)))
                  (let
                     ((_$2_3 _$2_2))
                     (=>
                        _$2_3
                        (let
                           ((_$2_7 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_7)
                               (x$2_0 x$2_0_old))
                              (=>
                                 (and
                                    (let
                                       ((_$1_1 (<= i.0$1_0_old 10)))
                                       (=>
                                          _$1_1
                                          (let
                                             ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                                             (=>
                                                (not _$1_5)
                                                (let
                                                   ((_$1_6 (+ i.0$1_0_old 1)))
                                                   (let
                                                      ((i.0$1_0 _$1_6)
                                                       (x$1_0 x$1_0_old))
                                                      false)))))))
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0 x$2_0)
                                       (=>
                                          (INV_42 i.0$1_0_old x$1_0_old i.0$2_0 x$2_0 result$1 result$2)
                                          (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old 10)))
            (=>
               (not _$2_1)
               (let
                  ((_$2_3 false))
                  (=>
                     _$2_3
                     (let
                        ((_$2_7 (+ i.0$2_0_old 1)))
                        (let
                           ((i.0$2_0 _$2_7)
                            (x$2_0 x$2_0_old))
                           (=>
                              (and
                                 (let
                                    ((_$1_1 (<= i.0$1_0_old 10)))
                                    (=>
                                       _$1_1
                                       (let
                                          ((_$1_5 (= i.0$1_0_old x$1_0_old)))
                                          (=>
                                             (not _$1_5)
                                             (let
                                                ((_$1_6 (+ i.0$1_0_old 1)))
                                                (let
                                                   ((i.0$1_0 _$1_6)
                                                    (x$1_0 x$1_0_old))
                                                   false)))))))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0 x$2_0)
                                    (=>
                                       (INV_42 i.0$1_0_old x$1_0_old i.0$2_0 x$2_0 result$1 result$2)
                                       (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2))))))))))))))
(check-sat)
(get-model)
