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
      ((x$1_0 Int)
       (x$2_0 Int)
       (result$1 Int)
       (result$2 Int))
      (=>
         (and
            (= x$1_0 x$2_0))
         (and
            (=>
               (INV_REC_f x$1_0 x$2_0 result$1 result$2)
               (= result$1 result$2))
            (INV_REC_f_PRE x$1_0 x$2_0)))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1))
                   (_$2_0 (> x$2_0_old 1)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (- x$2_0_old 2)))
                        (and
                           (INV_REC_f_PRE _$1_1 _$2_1)
                           (forall
                              ((_$1_2 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_f _$1_1 _$2_1 _$1_2 _$2_2)
                                 (let
                                    ((_$1_1 (- x$1_0_old 1))
                                     (_$1_3 (+ _$1_2 1)))
                                    (let
                                       ((.0$1_0 _$1_3))
                                       (let
                                          ((_$1_4 (< .0$1_0 0)))
                                          (=>
                                             _$1_4
                                             (let
                                                ((.1$1_0 0))
                                                (let
                                                   ((result$1 .1$1_0)
                                                    (_$2_1 (- x$2_0_old 2))
                                                    (_$2_3 (+ _$2_2 2)))
                                                   (let
                                                      ((.0$2_0 _$2_3))
                                                      (let
                                                         ((_$2_4 (< .0$2_0 0)))
                                                         (=>
                                                            _$2_4
                                                            (let
                                                               ((.1$2_0 0))
                                                               (let
                                                                  ((result$2 .1$2_0))
                                                                  (INV_REC_f x$1_0_old x$2_0_old result$1 result$2)))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1))
                   (_$2_0 (> x$2_0_old 1)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (- x$2_0_old 2)))
                        (and
                           (INV_REC_f_PRE _$1_1 _$2_1)
                           (forall
                              ((_$1_2 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_f _$1_1 _$2_1 _$1_2 _$2_2)
                                 (let
                                    ((_$1_1 (- x$1_0_old 1))
                                     (_$1_3 (+ _$1_2 1)))
                                    (let
                                       ((.0$1_0 _$1_3))
                                       (let
                                          ((_$1_4 (< .0$1_0 0)))
                                          (=>
                                             _$1_4
                                             (let
                                                ((.1$1_0 0))
                                                (let
                                                   ((result$1 .1$1_0)
                                                    (_$2_1 (- x$2_0_old 2))
                                                    (_$2_3 (+ _$2_2 2)))
                                                   (let
                                                      ((.0$2_0 _$2_3))
                                                      (let
                                                         ((_$2_4 (< .0$2_0 0)))
                                                         (=>
                                                            (not _$2_4)
                                                            (let
                                                               ((.1$2_0 .0$2_0))
                                                               (let
                                                                  ((result$2 .1$2_0))
                                                                  (INV_REC_f x$1_0_old x$2_0_old result$1 result$2)))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1))
                   (_$2_0 (> x$2_0_old 1)))
                  (=>
                     (not _$2_0)
                     (let
                        ((.0$2_0 x$2_0_old))
                        (let
                           ((_$2_4 (< .0$2_0 0)))
                           (=>
                              _$2_4
                              (let
                                 ((.1$2_0 0))
                                 (let
                                    ((result$2 .1$2_0))
                                    (and
                                       (INV_REC_f__1_PRE _$1_1)
                                       (forall
                                          ((_$1_2 Int))
                                          (=>
                                             (INV_REC_f__1 _$1_1 _$1_2)
                                             (let
                                                ((_$1_1 (- x$1_0_old 1))
                                                 (_$1_3 (+ _$1_2 1)))
                                                (let
                                                   ((.0$1_0 _$1_3))
                                                   (let
                                                      ((_$1_4 (< .0$1_0 0)))
                                                      (=>
                                                         _$1_4
                                                         (let
                                                            ((.1$1_0 0))
                                                            (let
                                                               ((result$1 .1$1_0))
                                                               (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1))
                   (_$2_0 (> x$2_0_old 1)))
                  (=>
                     (not _$2_0)
                     (let
                        ((.0$2_0 x$2_0_old))
                        (let
                           ((_$2_4 (< .0$2_0 0)))
                           (=>
                              (not _$2_4)
                              (let
                                 ((.1$2_0 .0$2_0))
                                 (let
                                    ((result$2 .1$2_0))
                                    (and
                                       (INV_REC_f__1_PRE _$1_1)
                                       (forall
                                          ((_$1_2 Int))
                                          (=>
                                             (INV_REC_f__1 _$1_1 _$1_2)
                                             (let
                                                ((_$1_1 (- x$1_0_old 1))
                                                 (_$1_3 (+ _$1_2 1)))
                                                (let
                                                   ((.0$1_0 _$1_3))
                                                   (let
                                                      ((_$1_4 (< .0$1_0 0)))
                                                      (=>
                                                         _$1_4
                                                         (let
                                                            ((.1$1_0 0))
                                                            (let
                                                               ((result$1 .1$1_0))
                                                               (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1))
                   (_$2_0 (> x$2_0_old 1)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (- x$2_0_old 2)))
                        (and
                           (INV_REC_f_PRE _$1_1 _$2_1)
                           (forall
                              ((_$1_2 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_f _$1_1 _$2_1 _$1_2 _$2_2)
                                 (let
                                    ((_$1_1 (- x$1_0_old 1))
                                     (_$1_3 (+ _$1_2 1)))
                                    (let
                                       ((.0$1_0 _$1_3))
                                       (let
                                          ((_$1_4 (< .0$1_0 0)))
                                          (=>
                                             (not _$1_4)
                                             (let
                                                ((.1$1_0 .0$1_0))
                                                (let
                                                   ((result$1 .1$1_0)
                                                    (_$2_1 (- x$2_0_old 2))
                                                    (_$2_3 (+ _$2_2 2)))
                                                   (let
                                                      ((.0$2_0 _$2_3))
                                                      (let
                                                         ((_$2_4 (< .0$2_0 0)))
                                                         (=>
                                                            _$2_4
                                                            (let
                                                               ((.1$2_0 0))
                                                               (let
                                                                  ((result$2 .1$2_0))
                                                                  (INV_REC_f x$1_0_old x$2_0_old result$1 result$2)))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1))
                   (_$2_0 (> x$2_0_old 1)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (- x$2_0_old 2)))
                        (and
                           (INV_REC_f_PRE _$1_1 _$2_1)
                           (forall
                              ((_$1_2 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_f _$1_1 _$2_1 _$1_2 _$2_2)
                                 (let
                                    ((_$1_1 (- x$1_0_old 1))
                                     (_$1_3 (+ _$1_2 1)))
                                    (let
                                       ((.0$1_0 _$1_3))
                                       (let
                                          ((_$1_4 (< .0$1_0 0)))
                                          (=>
                                             (not _$1_4)
                                             (let
                                                ((.1$1_0 .0$1_0))
                                                (let
                                                   ((result$1 .1$1_0)
                                                    (_$2_1 (- x$2_0_old 2))
                                                    (_$2_3 (+ _$2_2 2)))
                                                   (let
                                                      ((.0$2_0 _$2_3))
                                                      (let
                                                         ((_$2_4 (< .0$2_0 0)))
                                                         (=>
                                                            (not _$2_4)
                                                            (let
                                                               ((.1$2_0 .0$2_0))
                                                               (let
                                                                  ((result$2 .1$2_0))
                                                                  (INV_REC_f x$1_0_old x$2_0_old result$1 result$2)))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1))
                   (_$2_0 (> x$2_0_old 1)))
                  (=>
                     (not _$2_0)
                     (let
                        ((.0$2_0 x$2_0_old))
                        (let
                           ((_$2_4 (< .0$2_0 0)))
                           (=>
                              _$2_4
                              (let
                                 ((.1$2_0 0))
                                 (let
                                    ((result$2 .1$2_0))
                                    (and
                                       (INV_REC_f__1_PRE _$1_1)
                                       (forall
                                          ((_$1_2 Int))
                                          (=>
                                             (INV_REC_f__1 _$1_1 _$1_2)
                                             (let
                                                ((_$1_1 (- x$1_0_old 1))
                                                 (_$1_3 (+ _$1_2 1)))
                                                (let
                                                   ((.0$1_0 _$1_3))
                                                   (let
                                                      ((_$1_4 (< .0$1_0 0)))
                                                      (=>
                                                         (not _$1_4)
                                                         (let
                                                            ((.1$1_0 .0$1_0))
                                                            (let
                                                               ((result$1 .1$1_0))
                                                               (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1))
                   (_$2_0 (> x$2_0_old 1)))
                  (=>
                     (not _$2_0)
                     (let
                        ((.0$2_0 x$2_0_old))
                        (let
                           ((_$2_4 (< .0$2_0 0)))
                           (=>
                              (not _$2_4)
                              (let
                                 ((.1$2_0 .0$2_0))
                                 (let
                                    ((result$2 .1$2_0))
                                    (and
                                       (INV_REC_f__1_PRE _$1_1)
                                       (forall
                                          ((_$1_2 Int))
                                          (=>
                                             (INV_REC_f__1 _$1_1 _$1_2)
                                             (let
                                                ((_$1_1 (- x$1_0_old 1))
                                                 (_$1_3 (+ _$1_2 1)))
                                                (let
                                                   ((.0$1_0 _$1_3))
                                                   (let
                                                      ((_$1_4 (< .0$1_0 0)))
                                                      (=>
                                                         (not _$1_4)
                                                         (let
                                                            ((.1$1_0 .0$1_0))
                                                            (let
                                                               ((result$1 .1$1_0))
                                                               (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        _$1_4
                        (let
                           ((.1$1_0 0))
                           (let
                              ((result$1 .1$1_0)
                               (_$2_0 (> x$2_0_old 1)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (- x$2_0_old 2)))
                                    (and
                                       (INV_REC_f__2_PRE _$2_1)
                                       (forall
                                          ((_$2_2 Int))
                                          (=>
                                             (INV_REC_f__2 _$2_1 _$2_2)
                                             (let
                                                ((_$2_1 (- x$2_0_old 2))
                                                 (_$2_3 (+ _$2_2 2)))
                                                (let
                                                   ((.0$2_0 _$2_3))
                                                   (let
                                                      ((_$2_4 (< .0$2_0 0)))
                                                      (=>
                                                         _$2_4
                                                         (let
                                                            ((.1$2_0 0))
                                                            (let
                                                               ((result$2 .1$2_0))
                                                               (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        _$1_4
                        (let
                           ((.1$1_0 0))
                           (let
                              ((result$1 .1$1_0)
                               (_$2_0 (> x$2_0_old 1)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (- x$2_0_old 2)))
                                    (and
                                       (INV_REC_f__2_PRE _$2_1)
                                       (forall
                                          ((_$2_2 Int))
                                          (=>
                                             (INV_REC_f__2 _$2_1 _$2_2)
                                             (let
                                                ((_$2_1 (- x$2_0_old 2))
                                                 (_$2_3 (+ _$2_2 2)))
                                                (let
                                                   ((.0$2_0 _$2_3))
                                                   (let
                                                      ((_$2_4 (< .0$2_0 0)))
                                                      (=>
                                                         (not _$2_4)
                                                         (let
                                                            ((.1$2_0 .0$2_0))
                                                            (let
                                                               ((result$2 .1$2_0))
                                                               (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        _$1_4
                        (let
                           ((.1$1_0 0))
                           (let
                              ((result$1 .1$1_0)
                               (_$2_0 (> x$2_0_old 1)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((.0$2_0 x$2_0_old))
                                    (let
                                       ((_$2_4 (< .0$2_0 0)))
                                       (=>
                                          _$2_4
                                          (let
                                             ((.1$2_0 0))
                                             (let
                                                ((result$2 .1$2_0))
                                                (INV_REC_f x$1_0_old x$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        _$1_4
                        (let
                           ((.1$1_0 0))
                           (let
                              ((result$1 .1$1_0)
                               (_$2_0 (> x$2_0_old 1)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((.0$2_0 x$2_0_old))
                                    (let
                                       ((_$2_4 (< .0$2_0 0)))
                                       (=>
                                          (not _$2_4)
                                          (let
                                             ((.1$2_0 .0$2_0))
                                             (let
                                                ((result$2 .1$2_0))
                                                (INV_REC_f x$1_0_old x$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        (not _$1_4)
                        (let
                           ((.1$1_0 .0$1_0))
                           (let
                              ((result$1 .1$1_0)
                               (_$2_0 (> x$2_0_old 1)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (- x$2_0_old 2)))
                                    (and
                                       (INV_REC_f__2_PRE _$2_1)
                                       (forall
                                          ((_$2_2 Int))
                                          (=>
                                             (INV_REC_f__2 _$2_1 _$2_2)
                                             (let
                                                ((_$2_1 (- x$2_0_old 2))
                                                 (_$2_3 (+ _$2_2 2)))
                                                (let
                                                   ((.0$2_0 _$2_3))
                                                   (let
                                                      ((_$2_4 (< .0$2_0 0)))
                                                      (=>
                                                         _$2_4
                                                         (let
                                                            ((.1$2_0 0))
                                                            (let
                                                               ((result$2 .1$2_0))
                                                               (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        (not _$1_4)
                        (let
                           ((.1$1_0 .0$1_0))
                           (let
                              ((result$1 .1$1_0)
                               (_$2_0 (> x$2_0_old 1)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (- x$2_0_old 2)))
                                    (and
                                       (INV_REC_f__2_PRE _$2_1)
                                       (forall
                                          ((_$2_2 Int))
                                          (=>
                                             (INV_REC_f__2 _$2_1 _$2_2)
                                             (let
                                                ((_$2_1 (- x$2_0_old 2))
                                                 (_$2_3 (+ _$2_2 2)))
                                                (let
                                                   ((.0$2_0 _$2_3))
                                                   (let
                                                      ((_$2_4 (< .0$2_0 0)))
                                                      (=>
                                                         (not _$2_4)
                                                         (let
                                                            ((.1$2_0 .0$2_0))
                                                            (let
                                                               ((result$2 .1$2_0))
                                                               (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        (not _$1_4)
                        (let
                           ((.1$1_0 .0$1_0))
                           (let
                              ((result$1 .1$1_0)
                               (_$2_0 (> x$2_0_old 1)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((.0$2_0 x$2_0_old))
                                    (let
                                       ((_$2_4 (< .0$2_0 0)))
                                       (=>
                                          _$2_4
                                          (let
                                             ((.1$2_0 0))
                                             (let
                                                ((result$2 .1$2_0))
                                                (INV_REC_f x$1_0_old x$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        (not _$1_4)
                        (let
                           ((.1$1_0 .0$1_0))
                           (let
                              ((result$1 .1$1_0)
                               (_$2_0 (> x$2_0_old 1)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((.0$2_0 x$2_0_old))
                                    (let
                                       ((_$2_4 (< .0$2_0 0)))
                                       (=>
                                          (not _$2_4)
                                          (let
                                             ((.1$2_0 .0$2_0))
                                             (let
                                                ((result$2 .1$2_0))
                                                (INV_REC_f x$1_0_old x$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE x$1_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1)))
                  (and
                     (INV_REC_f__1_PRE _$1_1)
                     (forall
                        ((_$1_2 Int))
                        (=>
                           (INV_REC_f__1 _$1_1 _$1_2)
                           (let
                              ((_$1_1 (- x$1_0_old 1))
                               (_$1_3 (+ _$1_2 1)))
                              (let
                                 ((.0$1_0 _$1_3))
                                 (let
                                    ((_$1_4 (< .0$1_0 0)))
                                    (=>
                                       _$1_4
                                       (let
                                          ((.1$1_0 0))
                                          (let
                                             ((result$1 .1$1_0))
                                             (INV_REC_f__1 x$1_0_old result$1))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE x$1_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- x$1_0_old 1)))
                  (and
                     (INV_REC_f__1_PRE _$1_1)
                     (forall
                        ((_$1_2 Int))
                        (=>
                           (INV_REC_f__1 _$1_1 _$1_2)
                           (let
                              ((_$1_1 (- x$1_0_old 1))
                               (_$1_3 (+ _$1_2 1)))
                              (let
                                 ((.0$1_0 _$1_3))
                                 (let
                                    ((_$1_4 (< .0$1_0 0)))
                                    (=>
                                       (not _$1_4)
                                       (let
                                          ((.1$1_0 .0$1_0))
                                          (let
                                             ((result$1 .1$1_0))
                                             (INV_REC_f__1 x$1_0_old result$1))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE x$1_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        _$1_4
                        (let
                           ((.1$1_0 0))
                           (let
                              ((result$1 .1$1_0))
                              (INV_REC_f__1 x$1_0_old result$1)))))))))))
(assert
   (forall
      ((x$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE x$1_0_old)
         (let
            ((_$1_0 (> x$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((.0$1_0 x$1_0_old))
                  (let
                     ((_$1_4 (< .0$1_0 0)))
                     (=>
                        (not _$1_4)
                        (let
                           ((.1$1_0 .0$1_0))
                           (let
                              ((result$1 .1$1_0))
                              (INV_REC_f__1 x$1_0_old result$1)))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old)
         (let
            ((_$2_0 (> x$2_0_old 1)))
            (=>
               _$2_0
               (let
                  ((_$2_1 (- x$2_0_old 2)))
                  (and
                     (INV_REC_f__2_PRE _$2_1)
                     (forall
                        ((_$2_2 Int))
                        (=>
                           (INV_REC_f__2 _$2_1 _$2_2)
                           (let
                              ((_$2_1 (- x$2_0_old 2))
                               (_$2_3 (+ _$2_2 2)))
                              (let
                                 ((.0$2_0 _$2_3))
                                 (let
                                    ((_$2_4 (< .0$2_0 0)))
                                    (=>
                                       _$2_4
                                       (let
                                          ((.1$2_0 0))
                                          (let
                                             ((result$2 .1$2_0))
                                             (INV_REC_f__2 x$2_0_old result$2))))))))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old)
         (let
            ((_$2_0 (> x$2_0_old 1)))
            (=>
               _$2_0
               (let
                  ((_$2_1 (- x$2_0_old 2)))
                  (and
                     (INV_REC_f__2_PRE _$2_1)
                     (forall
                        ((_$2_2 Int))
                        (=>
                           (INV_REC_f__2 _$2_1 _$2_2)
                           (let
                              ((_$2_1 (- x$2_0_old 2))
                               (_$2_3 (+ _$2_2 2)))
                              (let
                                 ((.0$2_0 _$2_3))
                                 (let
                                    ((_$2_4 (< .0$2_0 0)))
                                    (=>
                                       (not _$2_4)
                                       (let
                                          ((.1$2_0 .0$2_0))
                                          (let
                                             ((result$2 .1$2_0))
                                             (INV_REC_f__2 x$2_0_old result$2))))))))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old)
         (let
            ((_$2_0 (> x$2_0_old 1)))
            (=>
               (not _$2_0)
               (let
                  ((.0$2_0 x$2_0_old))
                  (let
                     ((_$2_4 (< .0$2_0 0)))
                     (=>
                        _$2_4
                        (let
                           ((.1$2_0 0))
                           (let
                              ((result$2 .1$2_0))
                              (INV_REC_f__2 x$2_0_old result$2)))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old)
         (let
            ((_$2_0 (> x$2_0_old 1)))
            (=>
               (not _$2_0)
               (let
                  ((.0$2_0 x$2_0_old))
                  (let
                     ((_$2_4 (< .0$2_0 0)))
                     (=>
                        (not _$2_4)
                        (let
                           ((.1$2_0 .0$2_0))
                           (let
                              ((result$2 .1$2_0))
                              (INV_REC_f__2 x$2_0_old result$2)))))))))))
; FORBIDDEN PATHS
; OFF BY N
(check-sat)
(get-model)
