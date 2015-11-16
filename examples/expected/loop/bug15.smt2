(set-logic HORN)
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
   INV_REC_f__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_42
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_42__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_42__2
   (Int
    Int)
   Bool)
(assert
   (forall
      ((z$1_0 Int)
       (z$2_0 Int)
       (result$1 Int)
       (result$2 Int))
      (=>
         (and
            (= z$1_0 z$2_0))
         (and
            (=>
               (INV_REC_f z$1_0 z$2_0 result$1 result$2)
               (= result$1 result$2))
            (INV_REC_f_PRE z$1_0 z$2_0)))))
(assert
   (forall
      ((z$1_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE z$1_0_old z$2_0_old)
         (let
            ((x.0$1_0 1))
            (let
               ((_$1_0 (<= x.0$1_0 9)))
               (=>
                  (not _$1_0)
                  (let
                     ((_$1_3 (* 2 x.0$1_0)))
                     (let
                        ((result$1 _$1_3)
                         (x.0$2_0 1))
                        (let
                           ((_$2_0 (< x.0$2_0 10)))
                           (=>
                              (not _$2_0)
                              (let
                                 ((_$2_3 (* x.0$2_0 2)))
                                 (let
                                    ((result$2 _$2_3))
                                    (INV_REC_f z$1_0_old z$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((z$1_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE z$1_0_old z$2_0_old)
         (let
            ((x.0$1_0 1))
            (let
               ((_$1_0 (<= x.0$1_0 9)))
               (=>
                  _$1_0
                  (let
                     ((x.0$2_0 1))
                     (let
                        ((_$2_0 (< x.0$2_0 10)))
                        (=>
                           _$2_0
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_42_PRE x.0$1_0 x.0$2_0)
                                 (=>
                                    (INV_42 x.0$1_0 x.0$2_0 result$1 result$2)
                                    (INV_REC_f z$1_0_old z$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE x.0$1_0_old x.0$2_0_old)
         (let
            ((_$1_1 (+ x.0$1_0_old 2)))
            (let
               ((_$1_2 (* 2 _$1_1)))
               (let
                  ((x.0$1_0 _$1_2))
                  (let
                     ((_$1_0 (<= x.0$1_0 9)))
                     (=>
                        (not _$1_0)
                        (let
                           ((_$1_3 (* 2 x.0$1_0)))
                           (let
                              ((result$1 _$1_3)
                               (_$2_1 (+ 2 x.0$2_0_old)))
                              (let
                                 ((_$2_2 (+ _$2_1 _$2_1)))
                                 (let
                                    ((x.0$2_0 _$2_2))
                                    (let
                                       ((_$2_0 (< x.0$2_0 10)))
                                       (=>
                                          (not _$2_0)
                                          (let
                                             ((_$2_3 (* x.0$2_0 2)))
                                             (let
                                                ((result$2 _$2_3))
                                                (INV_42 x.0$1_0_old x.0$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE x.0$1_0_old x.0$2_0_old)
         (let
            ((_$1_1 (+ x.0$1_0_old 2)))
            (let
               ((_$1_2 (* 2 _$1_1)))
               (let
                  ((x.0$1_0 _$1_2))
                  (let
                     ((_$1_0 (<= x.0$1_0 9)))
                     (=>
                        _$1_0
                        (let
                           ((_$2_1 (+ 2 x.0$2_0_old)))
                           (let
                              ((_$2_2 (+ _$2_1 _$2_1)))
                              (let
                                 ((x.0$2_0 _$2_2))
                                 (let
                                    ((_$2_0 (< x.0$2_0 10)))
                                    (=>
                                       _$2_0
                                       (forall
                                          ((result$1 Int)
                                           (result$2 Int))
                                          (and
                                             (INV_42_PRE x.0$1_0 x.0$2_0)
                                             (=>
                                                (INV_42 x.0$1_0 x.0$2_0 result$1 result$2)
                                                (INV_42 x.0$1_0_old x.0$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((z$1_0_old Int))
      (let
         ((x.0$1_0 1))
         (let
            ((_$1_0 (<= x.0$1_0 9)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_3 (* 2 x.0$1_0)))
                  (let
                     ((result$1 _$1_3))
                     (INV_REC_f__1 z$1_0_old result$1))))))))
(assert
   (forall
      ((z$1_0_old Int))
      (let
         ((x.0$1_0 1))
         (let
            ((_$1_0 (<= x.0$1_0 9)))
            (=>
               _$1_0
               (forall
                  ((result$1 Int))
                  (=>
                     (INV_42__1 x.0$1_0 result$1)
                     (INV_REC_f__1 z$1_0_old result$1))))))))
(assert
   (forall
      ((x.0$1_0_old Int))
      (let
         ((_$1_1 (+ x.0$1_0_old 2)))
         (let
            ((_$1_2 (* 2 _$1_1)))
            (let
               ((x.0$1_0 _$1_2))
               (let
                  ((_$1_0 (<= x.0$1_0 9)))
                  (=>
                     (not _$1_0)
                     (let
                        ((_$1_3 (* 2 x.0$1_0)))
                        (let
                           ((result$1 _$1_3))
                           (INV_42__1 x.0$1_0_old result$1))))))))))
(assert
   (forall
      ((x.0$1_0_old Int))
      (let
         ((_$1_1 (+ x.0$1_0_old 2)))
         (let
            ((_$1_2 (* 2 _$1_1)))
            (let
               ((x.0$1_0 _$1_2))
               (let
                  ((_$1_0 (<= x.0$1_0 9)))
                  (=>
                     _$1_0
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_42__1 x.0$1_0 result$1)
                           (INV_42__1 x.0$1_0_old result$1))))))))))
(assert
   (forall
      ((z$2_0_old Int))
      (let
         ((x.0$2_0 1))
         (let
            ((_$2_0 (< x.0$2_0 10)))
            (=>
               (not _$2_0)
               (let
                  ((_$2_3 (* x.0$2_0 2)))
                  (let
                     ((result$2 _$2_3))
                     (INV_REC_f__2 z$2_0_old result$2))))))))
(assert
   (forall
      ((z$2_0_old Int))
      (let
         ((x.0$2_0 1))
         (let
            ((_$2_0 (< x.0$2_0 10)))
            (=>
               _$2_0
               (forall
                  ((result$2 Int))
                  (=>
                     (INV_42__2 x.0$2_0 result$2)
                     (INV_REC_f__2 z$2_0_old result$2))))))))
(assert
   (forall
      ((x.0$2_0_old Int))
      (let
         ((_$2_1 (+ 2 x.0$2_0_old)))
         (let
            ((_$2_2 (+ _$2_1 _$2_1)))
            (let
               ((x.0$2_0 _$2_2))
               (let
                  ((_$2_0 (< x.0$2_0 10)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_3 (* x.0$2_0 2)))
                        (let
                           ((result$2 _$2_3))
                           (INV_42__2 x.0$2_0_old result$2))))))))))
(assert
   (forall
      ((x.0$2_0_old Int))
      (let
         ((_$2_1 (+ 2 x.0$2_0_old)))
         (let
            ((_$2_2 (+ _$2_1 _$2_1)))
            (let
               ((x.0$2_0 _$2_2))
               (let
                  ((_$2_0 (< x.0$2_0 10)))
                  (=>
                     _$2_0
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_42__2 x.0$2_0 result$2)
                           (INV_42__2 x.0$2_0_old result$2))))))))))
; FORBIDDEN PATHS
(assert
   (forall
      ((z$1_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE z$1_0_old z$2_0_old)
         (let
            ((x.0$1_0 1))
            (let
               ((_$1_0 (<= x.0$1_0 9)))
               (=>
                  (not _$1_0)
                  (let
                     ((_$1_3 (* 2 x.0$1_0)))
                     (let
                        ((result$1 _$1_3)
                         (x.0$2_0 1))
                        (let
                           ((_$2_0 (< x.0$2_0 10)))
                           (=>
                              _$2_0
                              false))))))))))
(assert
   (forall
      ((z$1_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE z$1_0_old z$2_0_old)
         (let
            ((x.0$1_0 1))
            (let
               ((_$1_0 (<= x.0$1_0 9)))
               (=>
                  _$1_0
                  (let
                     ((x.0$2_0 1))
                     (let
                        ((_$2_0 (< x.0$2_0 10)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_3 (* x.0$2_0 2)))
                              (let
                                 ((result$2 _$2_3))
                                 false)))))))))))
; OFF BY N
(assert
   (forall
      ((x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE x.0$1_0_old x.0$2_0_old)
         (let
            ((_$1_1 (+ x.0$1_0_old 2)))
            (let
               ((_$1_2 (* 2 _$1_1)))
               (let
                  ((x.0$1_0 _$1_2))
                  (let
                     ((_$1_0 (<= x.0$1_0 9)))
                     (=>
                        _$1_0
                        (=>
                           (and
                              (let
                                 ((_$2_1 (+ 2 x.0$2_0_old)))
                                 (let
                                    ((_$2_2 (+ _$2_1 _$2_1)))
                                    (let
                                       ((x.0$2_0 _$2_2))
                                       (let
                                          ((_$2_0 (< x.0$2_0 10)))
                                          (=>
                                             _$2_0
                                             false))))))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_42_PRE x.0$1_0 x.0$2_0_old)
                                 (=>
                                    (INV_42 x.0$1_0 x.0$2_0_old result$1 result$2)
                                    (INV_42 x.0$1_0_old x.0$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE x.0$1_0_old x.0$2_0_old)
         (let
            ((_$2_1 (+ 2 x.0$2_0_old)))
            (let
               ((_$2_2 (+ _$2_1 _$2_1)))
               (let
                  ((x.0$2_0 _$2_2))
                  (let
                     ((_$2_0 (< x.0$2_0 10)))
                     (=>
                        _$2_0
                        (=>
                           (and
                              (let
                                 ((_$1_1 (+ x.0$1_0_old 2)))
                                 (let
                                    ((_$1_2 (* 2 _$1_1)))
                                    (let
                                       ((x.0$1_0 _$1_2))
                                       (let
                                          ((_$1_0 (<= x.0$1_0 9)))
                                          (=>
                                             _$1_0
                                             false))))))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_42_PRE x.0$1_0_old x.0$2_0)
                                 (=>
                                    (INV_42 x.0$1_0_old x.0$2_0 result$1 result$2)
                                    (INV_42 x.0$1_0_old x.0$2_0_old result$1 result$2)))))))))))))
(check-sat)
(get-model)
