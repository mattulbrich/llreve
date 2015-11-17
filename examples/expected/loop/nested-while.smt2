(set-logic HORN)
(declare-fun
   INV_REC_f
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_23
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
   INV_23_PRE
   (Int
    Int
    Int
    Int
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
    Int)
   Bool)
(declare-fun
   INV_42_PRE
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_23__1
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_23__1_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_23__2
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_23__2_PRE
   (Int
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
      ((x$1_0 Int)
       (g$1_0 Int)
       (x$2_0 Int)
       (g$2_0 Int)
       (result$1 Int)
       (result$2 Int))
      (=>
         (and
            (= g$1_0 g$2_0)
            (= x$1_0 x$2_0))
         (and
            (=>
               (INV_REC_f x$1_0 g$1_0 x$2_0 g$2_0 result$1 result$2)
               (= result$1 result$2))
            (INV_REC_f_PRE x$1_0 g$1_0 x$2_0 g$2_0)))))
(assert
   (forall
      ((x$1_0_old Int)
       (g$1_0_old Int)
       (x$2_0_old Int)
       (g$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old g$1_0_old x$2_0_old g$2_0_old)
         (let
            ((i.0$1_0 0)
             (.01$1_0 g$1_0_old)
             (.0$1_0 x$1_0_old))
            (let
               ((_$1_0 (< i.0$1_0 .0$1_0)))
               (=>
                  (not _$1_0)
                  (let
                     ((result$1 .01$1_0)
                      (i.0$2_0 0)
                      (.01$2_0 g$2_0_old)
                      (.0$2_0 x$2_0_old))
                     (let
                        ((_$2_0 (< i.0$2_0 .0$2_0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((result$2 .01$2_0))
                              (INV_REC_f x$1_0_old g$1_0_old x$2_0_old g$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (g$1_0_old Int)
       (x$2_0_old Int)
       (g$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old g$1_0_old x$2_0_old g$2_0_old)
         (let
            ((i.0$1_0 0)
             (.01$1_0 g$1_0_old)
             (.0$1_0 x$1_0_old))
            (let
               ((_$1_0 (< i.0$1_0 .0$1_0)))
               (=>
                  _$1_0
                  (let
                     ((i.0$2_0 0)
                      (.01$2_0 g$2_0_old)
                      (.0$2_0 x$2_0_old))
                     (let
                        ((_$2_0 (< i.0$2_0 .0$2_0)))
                        (=>
                           _$2_0
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_23_PRE .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0)
                                 (=>
                                    (INV_23 .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0 result$1 result$2)
                                    (INV_REC_f x$1_0_old g$1_0_old x$2_0_old g$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (+ i.0$1_0_old 1))
             (_$1_2 (- .01$1_0_old 2)))
            (let
               ((_$1_3 (+ _$1_2 1)))
               (let
                  ((.12$1_0 _$1_3)
                   (.1$1_0 .0$1_0_old))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 (not _$1_0)
                                 (let
                                    ((result$1 .01$1_0)
                                     (_$2_1 (+ i.0$2_0_old 1))
                                     (_$2_2 (- .01$2_0_old 1)))
                                    (let
                                       ((.12$2_0 _$2_2)
                                        (.1$2_0 .0$2_0_old))
                                       (let
                                          ((_$2_3 (< .1$2_0 _$2_1)))
                                          (=>
                                             (not _$2_3)
                                             (let
                                                ((i.0$2_0 _$2_1)
                                                 (.01$2_0 .12$2_0)
                                                 (.0$2_0 .1$2_0))
                                                (let
                                                   ((_$2_0 (< i.0$2_0 .0$2_0)))
                                                   (=>
                                                      (not _$2_0)
                                                      (let
                                                         ((result$2 .01$2_0))
                                                         (INV_23 .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (+ i.0$1_0_old 1))
             (_$1_2 (- .01$1_0_old 2)))
            (let
               ((_$1_3 (+ _$1_2 1)))
               (let
                  ((.12$1_0 _$1_3)
                   (.1$1_0 .0$1_0_old))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 _$1_0
                                 (let
                                    ((_$2_1 (+ i.0$2_0_old 1))
                                     (_$2_2 (- .01$2_0_old 1)))
                                    (let
                                       ((.12$2_0 _$2_2)
                                        (.1$2_0 .0$2_0_old))
                                       (let
                                          ((_$2_3 (< .1$2_0 _$2_1)))
                                          (=>
                                             (not _$2_3)
                                             (let
                                                ((i.0$2_0 _$2_1)
                                                 (.01$2_0 .12$2_0)
                                                 (.0$2_0 .1$2_0))
                                                (let
                                                   ((_$2_0 (< i.0$2_0 .0$2_0)))
                                                   (=>
                                                      _$2_0
                                                      (forall
                                                         ((result$1 Int)
                                                          (result$2 Int))
                                                         (and
                                                            (INV_23_PRE .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0)
                                                            (=>
                                                               (INV_23 .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0 result$1 result$2)
                                                               (INV_23 .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (+ i.0$1_0_old 1))
             (_$1_2 (- .01$1_0_old 2)))
            (let
               ((_$1_3 (+ _$1_2 1)))
               (let
                  ((.12$1_0 _$1_3)
                   (.1$1_0 .0$1_0_old))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1)))
                     (=>
                        _$1_4
                        (let
                           ((_$2_1 (+ i.0$2_0_old 1))
                            (_$2_2 (- .01$2_0_old 1)))
                           (let
                              ((.12$2_0 _$2_2)
                               (.1$2_0 .0$2_0_old))
                              (let
                                 ((_$2_3 (< .1$2_0 _$2_1)))
                                 (=>
                                    _$2_3
                                    (forall
                                       ((result$1 Int)
                                        (result$2 Int))
                                       (and
                                          (INV_42_PRE .1$1_0 .12$1_0 _$1_1 .1$2_0 .12$2_0 _$2_1)
                                          (=>
                                             (INV_42 .1$1_0 .12$1_0 _$1_1 .1$2_0 .12$2_0 _$2_1 result$1 result$2)
                                             (INV_23 .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42_PRE .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$1_5 (+ .1$1_0_old 2)))
            (let
               ((_$1_6 (- _$1_5 1))
                (_$1_7 (+ .12$1_0_old 1)))
               (let
                  ((.12$1_0 _$1_7)
                   (.1$1_0 _$1_6))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1_old)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1_old)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 (not _$1_0)
                                 (let
                                    ((result$1 .01$1_0)
                                     (_$2_4 (+ .1$2_0_old 1))
                                     (_$2_5 (+ .12$2_0_old 1)))
                                    (let
                                       ((.12$2_0 _$2_5)
                                        (.1$2_0 _$2_4))
                                       (let
                                          ((_$2_3 (< .1$2_0 _$2_1_old)))
                                          (=>
                                             (not _$2_3)
                                             (let
                                                ((i.0$2_0 _$2_1_old)
                                                 (.01$2_0 .12$2_0)
                                                 (.0$2_0 .1$2_0))
                                                (let
                                                   ((_$2_0 (< i.0$2_0 .0$2_0)))
                                                   (=>
                                                      (not _$2_0)
                                                      (let
                                                         ((result$2 .01$2_0))
                                                         (INV_42 .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42_PRE .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$1_5 (+ .1$1_0_old 2)))
            (let
               ((_$1_6 (- _$1_5 1))
                (_$1_7 (+ .12$1_0_old 1)))
               (let
                  ((.12$1_0 _$1_7)
                   (.1$1_0 _$1_6))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1_old)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1_old)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 _$1_0
                                 (let
                                    ((_$2_4 (+ .1$2_0_old 1))
                                     (_$2_5 (+ .12$2_0_old 1)))
                                    (let
                                       ((.12$2_0 _$2_5)
                                        (.1$2_0 _$2_4))
                                       (let
                                          ((_$2_3 (< .1$2_0 _$2_1_old)))
                                          (=>
                                             (not _$2_3)
                                             (let
                                                ((i.0$2_0 _$2_1_old)
                                                 (.01$2_0 .12$2_0)
                                                 (.0$2_0 .1$2_0))
                                                (let
                                                   ((_$2_0 (< i.0$2_0 .0$2_0)))
                                                   (=>
                                                      _$2_0
                                                      (forall
                                                         ((result$1 Int)
                                                          (result$2 Int))
                                                         (and
                                                            (INV_23_PRE .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0)
                                                            (=>
                                                               (INV_23 .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0 result$1 result$2)
                                                               (INV_42 .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42_PRE .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$1_5 (+ .1$1_0_old 2)))
            (let
               ((_$1_6 (- _$1_5 1))
                (_$1_7 (+ .12$1_0_old 1)))
               (let
                  ((.12$1_0 _$1_7)
                   (.1$1_0 _$1_6))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1_old)))
                     (=>
                        _$1_4
                        (let
                           ((_$1_1 _$1_1_old)
                            (_$2_4 (+ .1$2_0_old 1))
                            (_$2_5 (+ .12$2_0_old 1)))
                           (let
                              ((.12$2_0 _$2_5)
                               (.1$2_0 _$2_4))
                              (let
                                 ((_$2_3 (< .1$2_0 _$2_1_old)))
                                 (=>
                                    _$2_3
                                    (let
                                       ((_$2_1 _$2_1_old))
                                       (forall
                                          ((result$1 Int)
                                           (result$2 Int))
                                          (and
                                             (INV_42_PRE .1$1_0 .12$1_0 _$1_1 .1$2_0 .12$2_0 _$2_1)
                                             (=>
                                                (INV_42 .1$1_0 .12$1_0 _$1_1 .1$2_0 .12$2_0 _$2_1 result$1 result$2)
                                                (INV_42 .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (g$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE x$1_0_old g$1_0_old)
         (let
            ((i.0$1_0 0)
             (.01$1_0 g$1_0_old)
             (.0$1_0 x$1_0_old))
            (let
               ((_$1_0 (< i.0$1_0 .0$1_0)))
               (=>
                  (not _$1_0)
                  (let
                     ((result$1 .01$1_0))
                     (INV_REC_f__1 x$1_0_old g$1_0_old result$1))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (g$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE x$1_0_old g$1_0_old)
         (let
            ((i.0$1_0 0)
             (.01$1_0 g$1_0_old)
             (.0$1_0 x$1_0_old))
            (let
               ((_$1_0 (< i.0$1_0 .0$1_0)))
               (=>
                  _$1_0
                  (forall
                     ((result$1 Int))
                     (=>
                        (INV_23__1 .0$1_0 .01$1_0 i.0$1_0 result$1)
                        (INV_REC_f__1 x$1_0_old g$1_0_old result$1)))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int))
      (=>
         (INV_23__1_PRE .0$1_0_old .01$1_0_old i.0$1_0_old)
         (let
            ((_$1_1 (+ i.0$1_0_old 1))
             (_$1_2 (- .01$1_0_old 2)))
            (let
               ((_$1_3 (+ _$1_2 1)))
               (let
                  ((.12$1_0 _$1_3)
                   (.1$1_0 .0$1_0_old))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 (not _$1_0)
                                 (let
                                    ((result$1 .01$1_0))
                                    (INV_23__1 .0$1_0_old .01$1_0_old i.0$1_0_old result$1)))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int))
      (=>
         (INV_23__1_PRE .0$1_0_old .01$1_0_old i.0$1_0_old)
         (let
            ((_$1_1 (+ i.0$1_0_old 1))
             (_$1_2 (- .01$1_0_old 2)))
            (let
               ((_$1_3 (+ _$1_2 1)))
               (let
                  ((.12$1_0 _$1_3)
                   (.1$1_0 .0$1_0_old))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 _$1_0
                                 (forall
                                    ((result$1 Int))
                                    (=>
                                       (INV_23__1 .0$1_0 .01$1_0 i.0$1_0 result$1)
                                       (INV_23__1 .0$1_0_old .01$1_0_old i.0$1_0_old result$1))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int))
      (=>
         (INV_23__1_PRE .0$1_0_old .01$1_0_old i.0$1_0_old)
         (let
            ((_$1_1 (+ i.0$1_0_old 1))
             (_$1_2 (- .01$1_0_old 2)))
            (let
               ((_$1_3 (+ _$1_2 1)))
               (let
                  ((.12$1_0 _$1_3)
                   (.1$1_0 .0$1_0_old))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1)))
                     (=>
                        _$1_4
                        (forall
                           ((result$1 Int))
                           (=>
                              (INV_42__1 .1$1_0 .12$1_0 _$1_1 result$1)
                              (INV_23__1 .0$1_0_old .01$1_0_old i.0$1_0_old result$1)))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int))
      (=>
         (INV_42__1_PRE .1$1_0_old .12$1_0_old _$1_1_old)
         (let
            ((_$1_5 (+ .1$1_0_old 2)))
            (let
               ((_$1_6 (- _$1_5 1))
                (_$1_7 (+ .12$1_0_old 1)))
               (let
                  ((.12$1_0 _$1_7)
                   (.1$1_0 _$1_6))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1_old)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1_old)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 (not _$1_0)
                                 (let
                                    ((result$1 .01$1_0))
                                    (INV_42__1 .1$1_0_old .12$1_0_old _$1_1_old result$1)))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int))
      (=>
         (INV_42__1_PRE .1$1_0_old .12$1_0_old _$1_1_old)
         (let
            ((_$1_5 (+ .1$1_0_old 2)))
            (let
               ((_$1_6 (- _$1_5 1))
                (_$1_7 (+ .12$1_0_old 1)))
               (let
                  ((.12$1_0 _$1_7)
                   (.1$1_0 _$1_6))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1_old)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1_old)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 _$1_0
                                 (forall
                                    ((result$1 Int))
                                    (=>
                                       (INV_23__1 .0$1_0 .01$1_0 i.0$1_0 result$1)
                                       (INV_42__1 .1$1_0_old .12$1_0_old _$1_1_old result$1))))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int))
      (=>
         (INV_42__1_PRE .1$1_0_old .12$1_0_old _$1_1_old)
         (let
            ((_$1_5 (+ .1$1_0_old 2)))
            (let
               ((_$1_6 (- _$1_5 1))
                (_$1_7 (+ .12$1_0_old 1)))
               (let
                  ((.12$1_0 _$1_7)
                   (.1$1_0 _$1_6))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1_old)))
                     (=>
                        _$1_4
                        (let
                           ((_$1_1 _$1_1_old))
                           (forall
                              ((result$1 Int))
                              (=>
                                 (INV_42__1 .1$1_0 .12$1_0 _$1_1 result$1)
                                 (INV_42__1 .1$1_0_old .12$1_0_old _$1_1_old result$1))))))))))))
(assert
   (forall
      ((x$2_0_old Int)
       (g$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old g$2_0_old)
         (let
            ((i.0$2_0 0)
             (.01$2_0 g$2_0_old)
             (.0$2_0 x$2_0_old))
            (let
               ((_$2_0 (< i.0$2_0 .0$2_0)))
               (=>
                  (not _$2_0)
                  (let
                     ((result$2 .01$2_0))
                     (INV_REC_f__2 x$2_0_old g$2_0_old result$2))))))))
(assert
   (forall
      ((x$2_0_old Int)
       (g$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE x$2_0_old g$2_0_old)
         (let
            ((i.0$2_0 0)
             (.01$2_0 g$2_0_old)
             (.0$2_0 x$2_0_old))
            (let
               ((_$2_0 (< i.0$2_0 .0$2_0)))
               (=>
                  _$2_0
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_23__2 .0$2_0 .01$2_0 i.0$2_0 result$2)
                        (INV_REC_f__2 x$2_0_old g$2_0_old result$2)))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23__2_PRE .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$2_1 (+ i.0$2_0_old 1))
             (_$2_2 (- .01$2_0_old 1)))
            (let
               ((.12$2_0 _$2_2)
                (.1$2_0 .0$2_0_old))
               (let
                  ((_$2_3 (< .1$2_0 _$2_1)))
                  (=>
                     (not _$2_3)
                     (let
                        ((i.0$2_0 _$2_1)
                         (.01$2_0 .12$2_0)
                         (.0$2_0 .1$2_0))
                        (let
                           ((_$2_0 (< i.0$2_0 .0$2_0)))
                           (=>
                              (not _$2_0)
                              (let
                                 ((result$2 .01$2_0))
                                 (INV_23__2 .0$2_0_old .01$2_0_old i.0$2_0_old result$2))))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23__2_PRE .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$2_1 (+ i.0$2_0_old 1))
             (_$2_2 (- .01$2_0_old 1)))
            (let
               ((.12$2_0 _$2_2)
                (.1$2_0 .0$2_0_old))
               (let
                  ((_$2_3 (< .1$2_0 _$2_1)))
                  (=>
                     (not _$2_3)
                     (let
                        ((i.0$2_0 _$2_1)
                         (.01$2_0 .12$2_0)
                         (.0$2_0 .1$2_0))
                        (let
                           ((_$2_0 (< i.0$2_0 .0$2_0)))
                           (=>
                              _$2_0
                              (forall
                                 ((result$2 Int))
                                 (=>
                                    (INV_23__2 .0$2_0 .01$2_0 i.0$2_0 result$2)
                                    (INV_23__2 .0$2_0_old .01$2_0_old i.0$2_0_old result$2)))))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23__2_PRE .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$2_1 (+ i.0$2_0_old 1))
             (_$2_2 (- .01$2_0_old 1)))
            (let
               ((.12$2_0 _$2_2)
                (.1$2_0 .0$2_0_old))
               (let
                  ((_$2_3 (< .1$2_0 _$2_1)))
                  (=>
                     _$2_3
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_42__2 .1$2_0 .12$2_0 _$2_1 result$2)
                           (INV_23__2 .0$2_0_old .01$2_0_old i.0$2_0_old result$2))))))))))
(assert
   (forall
      ((.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42__2_PRE .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$2_4 (+ .1$2_0_old 1))
             (_$2_5 (+ .12$2_0_old 1)))
            (let
               ((.12$2_0 _$2_5)
                (.1$2_0 _$2_4))
               (let
                  ((_$2_3 (< .1$2_0 _$2_1_old)))
                  (=>
                     (not _$2_3)
                     (let
                        ((i.0$2_0 _$2_1_old)
                         (.01$2_0 .12$2_0)
                         (.0$2_0 .1$2_0))
                        (let
                           ((_$2_0 (< i.0$2_0 .0$2_0)))
                           (=>
                              (not _$2_0)
                              (let
                                 ((result$2 .01$2_0))
                                 (INV_42__2 .1$2_0_old .12$2_0_old _$2_1_old result$2))))))))))))
(assert
   (forall
      ((.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42__2_PRE .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$2_4 (+ .1$2_0_old 1))
             (_$2_5 (+ .12$2_0_old 1)))
            (let
               ((.12$2_0 _$2_5)
                (.1$2_0 _$2_4))
               (let
                  ((_$2_3 (< .1$2_0 _$2_1_old)))
                  (=>
                     (not _$2_3)
                     (let
                        ((i.0$2_0 _$2_1_old)
                         (.01$2_0 .12$2_0)
                         (.0$2_0 .1$2_0))
                        (let
                           ((_$2_0 (< i.0$2_0 .0$2_0)))
                           (=>
                              _$2_0
                              (forall
                                 ((result$2 Int))
                                 (=>
                                    (INV_23__2 .0$2_0 .01$2_0 i.0$2_0 result$2)
                                    (INV_42__2 .1$2_0_old .12$2_0_old _$2_1_old result$2)))))))))))))
(assert
   (forall
      ((.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42__2_PRE .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$2_4 (+ .1$2_0_old 1))
             (_$2_5 (+ .12$2_0_old 1)))
            (let
               ((.12$2_0 _$2_5)
                (.1$2_0 _$2_4))
               (let
                  ((_$2_3 (< .1$2_0 _$2_1_old)))
                  (=>
                     _$2_3
                     (let
                        ((_$2_1 _$2_1_old))
                        (forall
                           ((result$2 Int))
                           (=>
                              (INV_42__2 .1$2_0 .12$2_0 _$2_1 result$2)
                              (INV_42__2 .1$2_0_old .12$2_0_old _$2_1_old result$2)))))))))))
; FORBIDDEN PATHS
(assert
   (forall
      ((x$1_0_old Int)
       (g$1_0_old Int)
       (x$2_0_old Int)
       (g$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old g$1_0_old x$2_0_old g$2_0_old)
         (let
            ((i.0$1_0 0)
             (.01$1_0 g$1_0_old)
             (.0$1_0 x$1_0_old))
            (let
               ((_$1_0 (< i.0$1_0 .0$1_0)))
               (=>
                  (not _$1_0)
                  (let
                     ((result$1 .01$1_0)
                      (i.0$2_0 0)
                      (.01$2_0 g$2_0_old)
                      (.0$2_0 x$2_0_old))
                     (let
                        ((_$2_0 (< i.0$2_0 .0$2_0)))
                        (=>
                           _$2_0
                           false)))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (g$1_0_old Int)
       (x$2_0_old Int)
       (g$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old g$1_0_old x$2_0_old g$2_0_old)
         (let
            ((i.0$1_0 0)
             (.01$1_0 g$1_0_old)
             (.0$1_0 x$1_0_old))
            (let
               ((_$1_0 (< i.0$1_0 .0$1_0)))
               (=>
                  _$1_0
                  (let
                     ((i.0$2_0 0)
                      (.01$2_0 g$2_0_old)
                      (.0$2_0 x$2_0_old))
                     (let
                        ((_$2_0 (< i.0$2_0 .0$2_0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((result$2 .01$2_0))
                              false))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (+ i.0$1_0_old 1))
             (_$1_2 (- .01$1_0_old 2)))
            (let
               ((_$1_3 (+ _$1_2 1)))
               (let
                  ((.12$1_0 _$1_3)
                   (.1$1_0 .0$1_0_old))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 (not _$1_0)
                                 (let
                                    ((result$1 .01$1_0)
                                     (_$2_1 (+ i.0$2_0_old 1))
                                     (_$2_2 (- .01$2_0_old 1)))
                                    (let
                                       ((.12$2_0 _$2_2)
                                        (.1$2_0 .0$2_0_old))
                                       (let
                                          ((_$2_3 (< .1$2_0 _$2_1)))
                                          (=>
                                             _$2_3
                                             false)))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (+ i.0$1_0_old 1))
             (_$1_2 (- .01$1_0_old 2)))
            (let
               ((_$1_3 (+ _$1_2 1)))
               (let
                  ((.12$1_0 _$1_3)
                   (.1$1_0 .0$1_0_old))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1)))
                     (=>
                        _$1_4
                        (let
                           ((_$2_1 (+ i.0$2_0_old 1))
                            (_$2_2 (- .01$2_0_old 1)))
                           (let
                              ((.12$2_0 _$2_2)
                               (.1$2_0 .0$2_0_old))
                              (let
                                 ((_$2_3 (< .1$2_0 _$2_1)))
                                 (=>
                                    (not _$2_3)
                                    (let
                                       ((i.0$2_0 _$2_1)
                                        (.01$2_0 .12$2_0)
                                        (.0$2_0 .1$2_0))
                                       (let
                                          ((_$2_0 (< i.0$2_0 .0$2_0)))
                                          (=>
                                             (not _$2_0)
                                             (let
                                                ((result$2 .01$2_0))
                                                false))))))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42_PRE .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$1_5 (+ .1$1_0_old 2)))
            (let
               ((_$1_6 (- _$1_5 1))
                (_$1_7 (+ .12$1_0_old 1)))
               (let
                  ((.12$1_0 _$1_7)
                   (.1$1_0 _$1_6))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1_old)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1_old)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 (not _$1_0)
                                 (let
                                    ((result$1 .01$1_0)
                                     (_$2_4 (+ .1$2_0_old 1))
                                     (_$2_5 (+ .12$2_0_old 1)))
                                    (let
                                       ((.12$2_0 _$2_5)
                                        (.1$2_0 _$2_4))
                                       (let
                                          ((_$2_3 (< .1$2_0 _$2_1_old)))
                                          (=>
                                             (not _$2_3)
                                             (let
                                                ((i.0$2_0 _$2_1_old)
                                                 (.01$2_0 .12$2_0)
                                                 (.0$2_0 .1$2_0))
                                                (let
                                                   ((_$2_0 (< i.0$2_0 .0$2_0)))
                                                   (=>
                                                      _$2_0
                                                      false))))))))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42_PRE .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$1_5 (+ .1$1_0_old 2)))
            (let
               ((_$1_6 (- _$1_5 1))
                (_$1_7 (+ .12$1_0_old 1)))
               (let
                  ((.12$1_0 _$1_7)
                   (.1$1_0 _$1_6))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1_old)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1_old)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 _$1_0
                                 (let
                                    ((_$2_4 (+ .1$2_0_old 1))
                                     (_$2_5 (+ .12$2_0_old 1)))
                                    (let
                                       ((.12$2_0 _$2_5)
                                        (.1$2_0 _$2_4))
                                       (let
                                          ((_$2_3 (< .1$2_0 _$2_1_old)))
                                          (=>
                                             (not _$2_3)
                                             (let
                                                ((i.0$2_0 _$2_1_old)
                                                 (.01$2_0 .12$2_0)
                                                 (.0$2_0 .1$2_0))
                                                (let
                                                   ((_$2_0 (< i.0$2_0 .0$2_0)))
                                                   (=>
                                                      (not _$2_0)
                                                      (let
                                                         ((result$2 .01$2_0))
                                                         false)))))))))))))))))))
; OFF BY N
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (+ i.0$1_0_old 1))
             (_$1_2 (- .01$1_0_old 2)))
            (let
               ((_$1_3 (+ _$1_2 1)))
               (let
                  ((.12$1_0 _$1_3)
                   (.1$1_0 .0$1_0_old))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1)))
                     (=>
                        (not _$1_4)
                        (let
                           ((i.0$1_0 _$1_1)
                            (.01$1_0 .12$1_0)
                            (.0$1_0 .1$1_0))
                           (let
                              ((_$1_0 (< i.0$1_0 .0$1_0)))
                              (=>
                                 _$1_0
                                 (=>
                                    (and
                                       (let
                                          ((_$2_1 (+ i.0$2_0_old 1))
                                           (_$2_2 (- .01$2_0_old 1)))
                                          (let
                                             ((.12$2_0 _$2_2)
                                              (.1$2_0 .0$2_0_old))
                                             (let
                                                ((_$2_3 (< .1$2_0 _$2_1)))
                                                (=>
                                                   (not _$2_3)
                                                   (let
                                                      ((i.0$2_0 _$2_1)
                                                       (.01$2_0 .12$2_0)
                                                       (.0$2_0 .1$2_0))
                                                      (let
                                                         ((_$2_0 (< i.0$2_0 .0$2_0)))
                                                         (=>
                                                            _$2_0
                                                            false))))))))
                                    (forall
                                       ((result$1 Int)
                                        (result$2 Int))
                                       (and
                                          (INV_23_PRE .0$1_0 .01$1_0 i.0$1_0 .0$2_0_old .01$2_0_old i.0$2_0_old)
                                          (=>
                                             (INV_23 .0$1_0 .01$1_0 i.0$1_0 .0$2_0_old .01$2_0_old i.0$2_0_old result$1 result$2)
                                             (INV_23 .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42_PRE .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$1_5 (+ .1$1_0_old 2)))
            (let
               ((_$1_6 (- _$1_5 1))
                (_$1_7 (+ .12$1_0_old 1)))
               (let
                  ((.12$1_0 _$1_7)
                   (.1$1_0 _$1_6))
                  (let
                     ((_$1_4 (< .1$1_0 _$1_1_old)))
                     (=>
                        _$1_4
                        (let
                           ((_$1_1 _$1_1_old))
                           (=>
                              (and
                                 (let
                                    ((_$2_4 (+ .1$2_0_old 1))
                                     (_$2_5 (+ .12$2_0_old 1)))
                                    (let
                                       ((.12$2_0 _$2_5)
                                        (.1$2_0 _$2_4))
                                       (let
                                          ((_$2_3 (< .1$2_0 _$2_1_old)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_1 _$2_1_old))
                                                false))))))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_42_PRE .1$1_0 .12$1_0 _$1_1 .1$2_0_old .12$2_0_old _$2_1_old)
                                    (=>
                                       (INV_42 .1$1_0 .12$1_0 _$1_1 .1$2_0_old .12$2_0_old _$2_1_old result$1 result$2)
                                       (INV_42 .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old result$1 result$2))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$2_1 (+ i.0$2_0_old 1))
             (_$2_2 (- .01$2_0_old 1)))
            (let
               ((.12$2_0 _$2_2)
                (.1$2_0 .0$2_0_old))
               (let
                  ((_$2_3 (< .1$2_0 _$2_1)))
                  (=>
                     (not _$2_3)
                     (let
                        ((i.0$2_0 _$2_1)
                         (.01$2_0 .12$2_0)
                         (.0$2_0 .1$2_0))
                        (let
                           ((_$2_0 (< i.0$2_0 .0$2_0)))
                           (=>
                              _$2_0
                              (=>
                                 (and
                                    (let
                                       ((_$1_1 (+ i.0$1_0_old 1))
                                        (_$1_2 (- .01$1_0_old 2)))
                                       (let
                                          ((_$1_3 (+ _$1_2 1)))
                                          (let
                                             ((.12$1_0 _$1_3)
                                              (.1$1_0 .0$1_0_old))
                                             (let
                                                ((_$1_4 (< .1$1_0 _$1_1)))
                                                (=>
                                                   (not _$1_4)
                                                   (let
                                                      ((i.0$1_0 _$1_1)
                                                       (.01$1_0 .12$1_0)
                                                       (.0$1_0 .1$1_0))
                                                      (let
                                                         ((_$1_0 (< i.0$1_0 .0$1_0)))
                                                         (=>
                                                            _$1_0
                                                            false)))))))))
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_23_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0 .01$2_0 i.0$2_0)
                                       (=>
                                          (INV_23 .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0 .01$2_0 i.0$2_0 result$1 result$2)
                                          (INV_23 .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_1_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_1_old Int))
      (=>
         (INV_42_PRE .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old)
         (let
            ((_$2_4 (+ .1$2_0_old 1))
             (_$2_5 (+ .12$2_0_old 1)))
            (let
               ((.12$2_0 _$2_5)
                (.1$2_0 _$2_4))
               (let
                  ((_$2_3 (< .1$2_0 _$2_1_old)))
                  (=>
                     _$2_3
                     (let
                        ((_$2_1 _$2_1_old))
                        (=>
                           (and
                              (let
                                 ((_$1_5 (+ .1$1_0_old 2)))
                                 (let
                                    ((_$1_6 (- _$1_5 1))
                                     (_$1_7 (+ .12$1_0_old 1)))
                                    (let
                                       ((.12$1_0 _$1_7)
                                        (.1$1_0 _$1_6))
                                       (let
                                          ((_$1_4 (< .1$1_0 _$1_1_old)))
                                          (=>
                                             _$1_4
                                             (let
                                                ((_$1_1 _$1_1_old))
                                                false)))))))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_42_PRE .1$1_0_old .12$1_0_old _$1_1_old .1$2_0 .12$2_0 _$2_1)
                                 (=>
                                    (INV_42 .1$1_0_old .12$1_0_old _$1_1_old .1$2_0 .12$2_0 _$2_1 result$1 result$2)
                                    (INV_42 .1$1_0_old .12$1_0_old _$1_1_old .1$2_0_old .12$2_0_old _$2_1_old result$1 result$2)))))))))))))
(check-sat)
(get-model)
