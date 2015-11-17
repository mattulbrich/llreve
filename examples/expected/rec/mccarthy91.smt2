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
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (and
            (= a$1_0_old x$2_0_old))
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- a$1_0_old 10)))
                  (let
                     ((r.0$1_0 _$1_1))
                     (let
                        ((result$1 r.0$1_0)
                         (_$2_0 (< x$2_0_old 101)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (+ 11 x$2_0_old)))
                              (and
                                 (INV_REC_f__2_PRE _$2_1)
                                 (forall
                                    ((_$2_2 Int))
                                    (=>
                                       (INV_REC_f__2 _$2_1 _$2_2)
                                       (let
                                          ((_$2_1 (+ 11 x$2_0_old)))
                                          (and
                                             (INV_REC_f__2_PRE _$2_2)
                                             (forall
                                                ((_$2_3 Int))
                                                (=>
                                                   (INV_REC_f__2 _$2_2 _$2_3)
                                                   (let
                                                      ((_$2_1 (+ 11 x$2_0_old))
                                                       (r.0$2_0 _$2_3))
                                                      (let
                                                         ((result$2 r.0$2_0))
                                                         (= result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (and
            (= a$1_0_old x$2_0_old))
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- a$1_0_old 10)))
                  (let
                     ((r.0$1_0 _$1_1))
                     (let
                        ((result$1 r.0$1_0)
                         (_$2_0 (< x$2_0_old 101)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (- x$2_0_old 10)))
                              (let
                                 ((r.0$2_0 _$2_4))
                                 (let
                                    ((result$2 r.0$2_0))
                                    (= result$1 result$2)))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (and
            (= a$1_0_old x$2_0_old))
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (+ a$1_0_old 11))
                   (_$2_0 (< x$2_0_old 101)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (+ 11 x$2_0_old)))
                        (and
                           (INV_REC_f_PRE _$1_2 _$2_1)
                           (forall
                              ((_$1_3 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_f _$1_2 _$2_1 _$1_3 _$2_2)
                                 (let
                                    ((_$1_2 (+ a$1_0_old 11))
                                     (_$2_1 (+ 11 x$2_0_old)))
                                    (and
                                       (INV_REC_f_PRE _$1_3 _$2_2)
                                       (forall
                                          ((_$1_4 Int)
                                           (_$2_3 Int))
                                          (=>
                                             (INV_REC_f _$1_3 _$2_2 _$1_4 _$2_3)
                                             (let
                                                ((_$1_2 (+ a$1_0_old 11))
                                                 (r.0$1_0 _$1_4))
                                                (let
                                                   ((result$1 r.0$1_0)
                                                    (_$2_1 (+ 11 x$2_0_old))
                                                    (r.0$2_0 _$2_3))
                                                   (let
                                                      ((result$2 r.0$2_0))
                                                      (= result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (and
            (= a$1_0_old x$2_0_old))
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (+ a$1_0_old 11))
                   (_$2_0 (< x$2_0_old 101)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_4 (- x$2_0_old 10)))
                        (let
                           ((r.0$2_0 _$2_4))
                           (let
                              ((result$2 r.0$2_0))
                              (and
                                 (INV_REC_f__1_PRE _$1_2)
                                 (forall
                                    ((_$1_3 Int))
                                    (=>
                                       (INV_REC_f__1 _$1_2 _$1_3)
                                       (let
                                          ((_$1_2 (+ a$1_0_old 11)))
                                          (and
                                             (INV_REC_f__1_PRE _$1_3)
                                             (forall
                                                ((_$1_4 Int))
                                                (=>
                                                   (INV_REC_f__1 _$1_3 _$1_4)
                                                   (let
                                                      ((_$1_2 (+ a$1_0_old 11))
                                                       (r.0$1_0 _$1_4))
                                                      (let
                                                         ((result$1 r.0$1_0))
                                                         (= result$1 result$2))))))))))))))))))))
; forbidden main
; offbyn main
; end
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE a$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- a$1_0_old 10)))
                  (let
                     ((r.0$1_0 _$1_1))
                     (let
                        ((result$1 r.0$1_0)
                         (_$2_0 (< x$2_0_old 101)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (+ 11 x$2_0_old)))
                              (and
                                 (INV_REC_f__2_PRE _$2_1)
                                 (forall
                                    ((_$2_2 Int))
                                    (=>
                                       (INV_REC_f__2 _$2_1 _$2_2)
                                       (let
                                          ((_$2_1 (+ 11 x$2_0_old)))
                                          (and
                                             (INV_REC_f__2_PRE _$2_2)
                                             (forall
                                                ((_$2_3 Int))
                                                (=>
                                                   (INV_REC_f__2 _$2_2 _$2_3)
                                                   (let
                                                      ((_$2_1 (+ 11 x$2_0_old))
                                                       (r.0$2_0 _$2_3))
                                                      (let
                                                         ((result$2 r.0$2_0))
                                                         (INV_REC_f a$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE a$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- a$1_0_old 10)))
                  (let
                     ((r.0$1_0 _$1_1))
                     (let
                        ((result$1 r.0$1_0)
                         (_$2_0 (< x$2_0_old 101)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (- x$2_0_old 10)))
                              (let
                                 ((r.0$2_0 _$2_4))
                                 (let
                                    ((result$2 r.0$2_0))
                                    (INV_REC_f a$1_0_old x$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE a$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (+ a$1_0_old 11))
                   (_$2_0 (< x$2_0_old 101)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (+ 11 x$2_0_old)))
                        (and
                           (INV_REC_f_PRE _$1_2 _$2_1)
                           (forall
                              ((_$1_3 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_f _$1_2 _$2_1 _$1_3 _$2_2)
                                 (let
                                    ((_$1_2 (+ a$1_0_old 11))
                                     (_$2_1 (+ 11 x$2_0_old)))
                                    (and
                                       (INV_REC_f_PRE _$1_3 _$2_2)
                                       (forall
                                          ((_$1_4 Int)
                                           (_$2_3 Int))
                                          (=>
                                             (INV_REC_f _$1_3 _$2_2 _$1_4 _$2_3)
                                             (let
                                                ((_$1_2 (+ a$1_0_old 11))
                                                 (r.0$1_0 _$1_4))
                                                (let
                                                   ((result$1 r.0$1_0)
                                                    (_$2_1 (+ 11 x$2_0_old))
                                                    (r.0$2_0 _$2_3))
                                                   (let
                                                      ((result$2 r.0$2_0))
                                                      (INV_REC_f a$1_0_old x$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE a$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (+ a$1_0_old 11))
                   (_$2_0 (< x$2_0_old 101)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_4 (- x$2_0_old 10)))
                        (let
                           ((r.0$2_0 _$2_4))
                           (let
                              ((result$2 r.0$2_0))
                              (and
                                 (INV_REC_f__1_PRE _$1_2)
                                 (forall
                                    ((_$1_3 Int))
                                    (=>
                                       (INV_REC_f__1 _$1_2 _$1_3)
                                       (let
                                          ((_$1_2 (+ a$1_0_old 11)))
                                          (and
                                             (INV_REC_f__1_PRE _$1_3)
                                             (forall
                                                ((_$1_4 Int))
                                                (=>
                                                   (INV_REC_f__1 _$1_3 _$1_4)
                                                   (let
                                                      ((_$1_2 (+ a$1_0_old 11))
                                                       (r.0$1_0 _$1_4))
                                                      (let
                                                         ((result$1 r.0$1_0))
                                                         (INV_REC_f a$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((a$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE a$1_0_old)
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- a$1_0_old 10)))
                  (let
                     ((r.0$1_0 _$1_1))
                     (let
                        ((result$1 r.0$1_0))
                        (INV_REC_f__1 a$1_0_old result$1)))))))))
(assert
   (forall
      ((a$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE a$1_0_old)
         (let
            ((_$1_0 (> a$1_0_old 100)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (+ a$1_0_old 11)))
                  (and
                     (INV_REC_f__1_PRE _$1_2)
                     (forall
                        ((_$1_3 Int))
                        (=>
                           (INV_REC_f__1 _$1_2 _$1_3)
                           (let
                              ((_$1_2 (+ a$1_0_old 11)))
                              (and
                                 (INV_REC_f__1_PRE _$1_3)
                                 (forall
                                    ((_$1_4 Int))
                                    (=>
                                       (INV_REC_f__1 _$1_3 _$1_4)
                                       (let
                                          ((_$1_2 (+ a$1_0_old 11))
                                           (r.0$1_0 _$1_4))
                                          (let
                                             ((result$1 r.0$1_0))
                                             (INV_REC_f__1 a$1_0_old result$1))))))))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old)
         (let
            ((_$2_0 (< x$2_0_old 101)))
            (=>
               _$2_0
               (let
                  ((_$2_1 (+ 11 x$2_0_old)))
                  (and
                     (INV_REC_f__2_PRE _$2_1)
                     (forall
                        ((_$2_2 Int))
                        (=>
                           (INV_REC_f__2 _$2_1 _$2_2)
                           (let
                              ((_$2_1 (+ 11 x$2_0_old)))
                              (and
                                 (INV_REC_f__2_PRE _$2_2)
                                 (forall
                                    ((_$2_3 Int))
                                    (=>
                                       (INV_REC_f__2 _$2_2 _$2_3)
                                       (let
                                          ((_$2_1 (+ 11 x$2_0_old))
                                           (r.0$2_0 _$2_3))
                                          (let
                                             ((result$2 r.0$2_0))
                                             (INV_REC_f__2 x$2_0_old result$2))))))))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old)
         (let
            ((_$2_0 (< x$2_0_old 101)))
            (=>
               (not _$2_0)
               (let
                  ((_$2_4 (- x$2_0_old 10)))
                  (let
                     ((r.0$2_0 _$2_4))
                     (let
                        ((result$2 r.0$2_0))
                        (INV_REC_f__2 x$2_0_old result$2)))))))))
; FORBIDDEN PATHS
; OFF BY N
(check-sat)
(get-model)
