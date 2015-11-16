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
   INV_REC_f__2
   (Int
    Int
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
   INV_42__1
   (Int
    Int
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
   INV_42__2
   (Int
    Int
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
             (.0$1_0 x$1_0_old)
             (i.0$2_0 0)
             (.01$2_0 g$2_0_old)
             (.0$2_0 x$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_42_PRE .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0)
                  (=>
                     (INV_42 .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0 result$1 result$2)
                     (INV_REC_f x$1_0_old g$1_0_old x$2_0_old g$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_5_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_5_old Int))
      (=>
         (INV_23_PRE .1$1_0_old .12$1_0_old _$1_5_old .1$2_0_old .12$2_0_old _$2_5_old)
         (let
            ((_$1_9 (< .1$1_0_old _$1_5_old)))
            (=>
               _$1_9
               (let
                  ((_$1_13 (+ .1$1_0_old 2)))
                  (let
                     ((_$1_14 (- _$1_13 1))
                      (_$1_15 (+ .12$1_0_old 1)))
                     (let
                        ((.12$1_0 _$1_15)
                         (.1$1_0 _$1_14)
                         (_$1_5 _$1_5_old)
                         (_$2_8 (< .1$2_0_old _$2_5_old)))
                        (=>
                           _$2_8
                           (let
                              ((_$2_12 (+ .1$2_0_old 1))
                               (_$2_13 (+ .12$2_0_old 2)))
                              (let
                                 ((.12$2_0 _$2_13)
                                  (.1$2_0 _$2_12)
                                  (_$2_5 _$2_5_old))
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_23_PRE .1$1_0 .12$1_0 _$1_5 .1$2_0 .12$2_0 _$2_5)
                                       (=>
                                          (INV_23 .1$1_0 .12$1_0 _$1_5 .1$2_0 .12$2_0 _$2_5 result$1 result$2)
                                          (INV_23 .1$1_0_old .12$1_0_old _$1_5_old .1$2_0_old .12$2_0_old _$2_5_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_5_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_5_old Int))
      (=>
         (INV_23_PRE .1$1_0_old .12$1_0_old _$1_5_old .1$2_0_old .12$2_0_old _$2_5_old)
         (let
            ((_$1_9 (< .1$1_0_old _$1_5_old)))
            (=>
               (not _$1_9)
               (let
                  ((i.0$1_0 _$1_5_old)
                   (.01$1_0 .12$1_0_old)
                   (.0$1_0 .1$1_0_old)
                   (_$2_8 (< .1$2_0_old _$2_5_old)))
                  (=>
                     (not _$2_8)
                     (let
                        ((i.0$2_0 _$2_5_old)
                         (.01$2_0 .12$2_0_old)
                         (.0$2_0 .1$2_0_old))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_42_PRE .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0)
                              (=>
                                 (INV_42 .0$1_0 .01$1_0 i.0$1_0 .0$2_0 .01$2_0 i.0$2_0 result$1 result$2)
                                 (INV_23 .1$1_0_old .12$1_0_old _$1_5_old .1$2_0_old .12$2_0_old _$2_5_old result$1 result$2))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old .0$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 .01$1_0_old)
                   (_$2_1 (< i.0$2_0_old .0$2_0_old)))
                  (=>
                     (not _$2_1)
                     (let
                        ((result$2 .01$2_0_old))
                        (INV_42 .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old result$1 result$2)))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old .0$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ i.0$1_0_old 1))
                   (_$1_6 (- .01$1_0_old 2)))
                  (let
                     ((_$1_7 (+ _$1_6 1)))
                     (let
                        ((.12$1_0 _$1_7)
                         (.1$1_0 .0$1_0_old)
                         (_$2_1 (< i.0$2_0_old .0$2_0_old)))
                        (=>
                           _$2_1
                           (let
                              ((_$2_5 (+ i.0$2_0_old 1))
                               (_$2_6 (- .01$2_0_old 2)))
                              (let
                                 ((.12$2_0 _$2_6)
                                  (.1$2_0 .0$2_0_old))
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_23_PRE .1$1_0 .12$1_0 _$1_5 .1$2_0 .12$2_0 _$2_5)
                                       (=>
                                          (INV_23 .1$1_0 .12$1_0 _$1_5 .1$2_0 .12$2_0 _$2_5 result$1 result$2)
                                          (INV_42 .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (g$1_0_old Int))
      (let
         ((i.0$1_0 0)
          (.01$1_0 g$1_0_old)
          (.0$1_0 x$1_0_old))
         (forall
            ((result$1 Int))
            (=>
               (INV_42__1 .0$1_0 .01$1_0 i.0$1_0 result$1)
               (INV_REC_f__1 x$1_0_old g$1_0_old result$1))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_5_old Int))
      (let
         ((_$1_9 (< .1$1_0_old _$1_5_old)))
         (=>
            _$1_9
            (let
               ((_$1_13 (+ .1$1_0_old 2)))
               (let
                  ((_$1_14 (- _$1_13 1))
                   (_$1_15 (+ .12$1_0_old 1)))
                  (let
                     ((.12$1_0 _$1_15)
                      (.1$1_0 _$1_14)
                      (_$1_5 _$1_5_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_23__1 .1$1_0 .12$1_0 _$1_5 result$1)
                           (INV_23__1 .1$1_0_old .12$1_0_old _$1_5_old result$1))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_5_old Int))
      (let
         ((_$1_9 (< .1$1_0_old _$1_5_old)))
         (=>
            (not _$1_9)
            (let
               ((i.0$1_0 _$1_5_old)
                (.01$1_0 .12$1_0_old)
                (.0$1_0 .1$1_0_old))
               (forall
                  ((result$1 Int))
                  (=>
                     (INV_42__1 .0$1_0 .01$1_0 i.0$1_0 result$1)
                     (INV_23__1 .1$1_0_old .12$1_0_old _$1_5_old result$1))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int))
      (let
         ((_$1_1 (< i.0$1_0_old .0$1_0_old)))
         (=>
            (not _$1_1)
            (let
               ((result$1 .01$1_0_old))
               (INV_42__1 .0$1_0_old .01$1_0_old i.0$1_0_old result$1))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int))
      (let
         ((_$1_1 (< i.0$1_0_old .0$1_0_old)))
         (=>
            _$1_1
            (let
               ((_$1_5 (+ i.0$1_0_old 1))
                (_$1_6 (- .01$1_0_old 2)))
               (let
                  ((_$1_7 (+ _$1_6 1)))
                  (let
                     ((.12$1_0 _$1_7)
                      (.1$1_0 .0$1_0_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_23__1 .1$1_0 .12$1_0 _$1_5 result$1)
                           (INV_42__1 .0$1_0_old .01$1_0_old i.0$1_0_old result$1))))))))))
(assert
   (forall
      ((x$2_0_old Int)
       (g$2_0_old Int))
      (let
         ((i.0$2_0 0)
          (.01$2_0 g$2_0_old)
          (.0$2_0 x$2_0_old))
         (forall
            ((result$2 Int))
            (=>
               (INV_42__2 .0$2_0 .01$2_0 i.0$2_0 result$2)
               (INV_REC_f__2 x$2_0_old g$2_0_old result$2))))))
(assert
   (forall
      ((.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_5_old Int))
      (let
         ((_$2_8 (< .1$2_0_old _$2_5_old)))
         (=>
            _$2_8
            (let
               ((_$2_12 (+ .1$2_0_old 1))
                (_$2_13 (+ .12$2_0_old 2)))
               (let
                  ((.12$2_0 _$2_13)
                   (.1$2_0 _$2_12)
                   (_$2_5 _$2_5_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_23__2 .1$2_0 .12$2_0 _$2_5 result$2)
                        (INV_23__2 .1$2_0_old .12$2_0_old _$2_5_old result$2)))))))))
(assert
   (forall
      ((.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_5_old Int))
      (let
         ((_$2_8 (< .1$2_0_old _$2_5_old)))
         (=>
            (not _$2_8)
            (let
               ((i.0$2_0 _$2_5_old)
                (.01$2_0 .12$2_0_old)
                (.0$2_0 .1$2_0_old))
               (forall
                  ((result$2 Int))
                  (=>
                     (INV_42__2 .0$2_0 .01$2_0 i.0$2_0 result$2)
                     (INV_23__2 .1$2_0_old .12$2_0_old _$2_5_old result$2))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (let
         ((_$2_1 (< i.0$2_0_old .0$2_0_old)))
         (=>
            (not _$2_1)
            (let
               ((result$2 .01$2_0_old))
               (INV_42__2 .0$2_0_old .01$2_0_old i.0$2_0_old result$2))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (let
         ((_$2_1 (< i.0$2_0_old .0$2_0_old)))
         (=>
            _$2_1
            (let
               ((_$2_5 (+ i.0$2_0_old 1))
                (_$2_6 (- .01$2_0_old 2)))
               (let
                  ((.12$2_0 _$2_6)
                   (.1$2_0 .0$2_0_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_23__2 .1$2_0 .12$2_0 _$2_5 result$2)
                        (INV_42__2 .0$2_0_old .01$2_0_old i.0$2_0_old result$2)))))))))
; FORBIDDEN PATHS
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old .0$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 .01$1_0_old)
                   (_$2_1 (< i.0$2_0_old .0$2_0_old)))
                  (=>
                     _$2_1
                     (let
                        ((_$2_5 (+ i.0$2_0_old 1))
                         (_$2_6 (- .01$2_0_old 2)))
                        (let
                           ((.12$2_0 _$2_6)
                            (.1$2_0 .0$2_0_old))
                           false)))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (.01$1_0_old Int)
       (i.0$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old .01$1_0_old i.0$1_0_old .0$2_0_old .01$2_0_old i.0$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old .0$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ i.0$1_0_old 1))
                   (_$1_6 (- .01$1_0_old 2)))
                  (let
                     ((_$1_7 (+ _$1_6 1)))
                     (let
                        ((.12$1_0 _$1_7)
                         (.1$1_0 .0$1_0_old)
                         (_$2_1 (< i.0$2_0_old .0$2_0_old)))
                        (=>
                           (not _$2_1)
                           (let
                              ((result$2 .01$2_0_old))
                              false))))))))))
; OFF BY N
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_5_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_5_old Int))
      (=>
         (INV_23_PRE .1$1_0_old .12$1_0_old _$1_5_old .1$2_0_old .12$2_0_old _$2_5_old)
         (let
            ((_$1_9 (< .1$1_0_old _$1_5_old)))
            (=>
               _$1_9
               (let
                  ((_$1_13 (+ .1$1_0_old 2)))
                  (let
                     ((_$1_14 (- _$1_13 1))
                      (_$1_15 (+ .12$1_0_old 1)))
                     (let
                        ((.12$1_0 _$1_15)
                         (.1$1_0 _$1_14)
                         (_$1_5 _$1_5_old))
                        (=>
                           (and
                              (let
                                 ((_$2_8 (< .1$2_0_old _$2_5_old)))
                                 (=>
                                    _$2_8
                                    (let
                                       ((_$2_12 (+ .1$2_0_old 1))
                                        (_$2_13 (+ .12$2_0_old 2)))
                                       (let
                                          ((.12$2_0 _$2_13)
                                           (.1$2_0 _$2_12)
                                           (_$2_5 _$2_5_old))
                                          false)))))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_23_PRE .1$1_0 .12$1_0 _$1_5 .1$2_0_old .12$2_0_old _$2_5_old)
                                 (=>
                                    (INV_23 .1$1_0 .12$1_0 _$1_5 .1$2_0_old .12$2_0_old _$2_5_old result$1 result$2)
                                    (INV_23 .1$1_0_old .12$1_0_old _$1_5_old .1$2_0_old .12$2_0_old _$2_5_old result$1 result$2)))))))))))))
(assert
   (forall
      ((.1$1_0_old Int)
       (.12$1_0_old Int)
       (_$1_5_old Int)
       (.1$2_0_old Int)
       (.12$2_0_old Int)
       (_$2_5_old Int))
      (=>
         (INV_23_PRE .1$1_0_old .12$1_0_old _$1_5_old .1$2_0_old .12$2_0_old _$2_5_old)
         (let
            ((_$2_8 (< .1$2_0_old _$2_5_old)))
            (=>
               _$2_8
               (let
                  ((_$2_12 (+ .1$2_0_old 1))
                   (_$2_13 (+ .12$2_0_old 2)))
                  (let
                     ((.12$2_0 _$2_13)
                      (.1$2_0 _$2_12)
                      (_$2_5 _$2_5_old))
                     (=>
                        (and
                           (let
                              ((_$1_9 (< .1$1_0_old _$1_5_old)))
                              (=>
                                 _$1_9
                                 (let
                                    ((_$1_13 (+ .1$1_0_old 2)))
                                    (let
                                       ((_$1_14 (- _$1_13 1))
                                        (_$1_15 (+ .12$1_0_old 1)))
                                       (let
                                          ((.12$1_0 _$1_15)
                                           (.1$1_0 _$1_14)
                                           (_$1_5 _$1_5_old))
                                          false))))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_23_PRE .1$1_0_old .12$1_0_old _$1_5_old .1$2_0 .12$2_0 _$2_5)
                              (=>
                                 (INV_23 .1$1_0_old .12$1_0_old _$1_5_old .1$2_0 .12$2_0 _$2_5 result$1 result$2)
                                 (INV_23 .1$1_0_old .12$1_0_old _$1_5_old .1$2_0_old .12$2_0_old _$2_5_old result$1 result$2))))))))))))
(check-sat)
(get-model)
