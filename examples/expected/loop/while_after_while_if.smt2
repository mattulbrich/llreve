(set-logic HORN)
(declare-fun
   INV_13_MAIN
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_23_MAIN
   (Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42_MAIN
   (Int
    Int
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
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_13
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_13_PRE
   (Int
    Int
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
    Int)
   Bool)
(declare-fun
   INV_23_PRE
   (Int
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
    Int)
   Bool)
(declare-fun
   INV_13__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_13__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_23__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_23__1_PRE
   (Int)
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
   INV_13__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_13__2_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_23__2
   (Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_23__2_PRE
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
      ((t$1_0_old Int)
       (c$1_0_old Int)
       (r$1_0_old Int)
       (t$2_0_old Int)
       (c$2_0_old Int)
       (r$2_0_old Int))
      (=>
         (and
            (= t$1_0_old t$2_0_old)
            (= c$1_0_old c$2_0_old)
            (= r$1_0_old r$2_0_old))
         (let
            ((_$1_0 (< 0 t$1_0_old)))
            (=>
               (not _$1_0)
               (let
                  ((r$1_0 r$1_0_old)
                   (.0$2_0 c$2_0_old)
                   (x.0$2_0 0)
                   (r$2_0 r$2_0_old)
                   (t$2_0 t$2_0_old))
                  (INV_23_MAIN r$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0)))))))
(assert
   (forall
      ((t$1_0_old Int)
       (c$1_0_old Int)
       (r$1_0_old Int)
       (t$2_0_old Int)
       (c$2_0_old Int)
       (r$2_0_old Int))
      (=>
         (and
            (= t$1_0_old t$2_0_old)
            (= c$1_0_old c$2_0_old)
            (= r$1_0_old r$2_0_old))
         (let
            ((_$1_0 (< 0 t$1_0_old)))
            (=>
               _$1_0
               (let
                  ((.0$1_0 c$1_0_old)
                   (x.0$1_0 0)
                   (r$1_0 r$1_0_old)
                   (.0$2_0 c$2_0_old)
                   (x.0$2_0 0)
                   (r$2_0 r$2_0_old)
                   (t$2_0 t$2_0_old))
                  (INV_42_MAIN .0$1_0 r$1_0 x.0$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0)))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int)
       (.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13_MAIN .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old)
         (let
            ((_$1_10 (> .01$1_0_old 0)))
            (=>
               (not _$1_10)
               (let
                  ((result$1 x.2$1_0_old)
                   (_$2_11 (> .01$2_0_old 0)))
                  (=>
                     (not _$2_11)
                     (let
                        ((result$2 x.2$2_0_old))
                        (= result$1 result$2)))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int)
       (.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13_MAIN .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old)
         (let
            ((_$1_10 (> .01$1_0_old 0)))
            (=>
               _$1_10
               (let
                  ((_$1_14 (+ x.2$1_0_old 2))
                   (_$1_15 (+ .01$1_0_old (- 1))))
                  (let
                     ((.01$1_0 _$1_15)
                      (x.2$1_0 _$1_14)
                      (_$2_11 (> .01$2_0_old 0)))
                     (=>
                        _$2_11
                        (let
                           ((_$2_15 (+ x.2$2_0_old 2))
                            (_$2_16 (+ .01$2_0_old (- 1))))
                           (let
                              ((.01$2_0 _$2_16)
                               (x.2$2_0 _$2_15))
                              (INV_13_MAIN .01$1_0 x.2$1_0 .01$2_0 x.2$2_0)))))))))))
(assert
   (forall
      ((r$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_23_MAIN r$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((x.1$1_0 0))
            (let
               ((.01$1_0 r$1_0_old)
                (x.2$1_0 x.1$1_0)
                (_$2_3 (< 0 .0$2_0_old)))
               (=>
                  (not _$2_3)
                  (let
                     ((.01$2_0 r$2_0_old)
                      (x.2$2_0 x.0$2_0_old))
                     (INV_13_MAIN .01$1_0 x.2$1_0 .01$2_0 x.2$2_0))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               (not _$1_2)
               (let
                  ((x.1$1_0 x.0$1_0_old))
                  (let
                     ((.01$1_0 r$1_0_old)
                      (x.2$1_0 x.1$1_0)
                      (_$2_3 (< 0 .0$2_0_old)))
                     (=>
                        (not _$2_3)
                        (let
                           ((.01$2_0 r$2_0_old)
                            (x.2$2_0 x.0$2_0_old))
                           (INV_13_MAIN .01$1_0 x.2$1_0 .01$2_0 x.2$2_0))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ x.0$1_0_old 1))
                   (_$1_7 (+ .0$1_0_old (- 1))))
                  (let
                     ((.0$1_0 _$1_7)
                      (x.0$1_0 _$1_6)
                      (r$1_0 r$1_0_old)
                      (_$2_3 (< 0 .0$2_0_old)))
                     (=>
                        _$2_3
                        (let
                           ((_$2_7 (< 0 t$2_0_old)))
                           (=>
                              _$2_7
                              (let
                                 ((_$2_8 (+ x.0$2_0_old 1)))
                                 (let
                                    ((x.1$2_0 _$2_8)
                                     (_$2_9 (+ .0$2_0_old (- 1))))
                                    (let
                                       ((.0$2_0 _$2_9)
                                        (x.0$2_0 x.1$2_0)
                                        (r$2_0 r$2_0_old)
                                        (t$2_0 t$2_0_old))
                                       (INV_42_MAIN .0$1_0 r$1_0 x.0$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ x.0$1_0_old 1))
                   (_$1_7 (+ .0$1_0_old (- 1))))
                  (let
                     ((.0$1_0 _$1_7)
                      (x.0$1_0 _$1_6)
                      (r$1_0 r$1_0_old)
                      (_$2_3 (< 0 .0$2_0_old)))
                     (=>
                        _$2_3
                        (let
                           ((_$2_7 (< 0 t$2_0_old)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((x.1$2_0 x.0$2_0_old)
                                  (_$2_9 (+ .0$2_0_old (- 1))))
                                 (let
                                    ((.0$2_0 _$2_9)
                                     (x.0$2_0 x.1$2_0)
                                     (r$2_0 r$2_0_old)
                                     (t$2_0 t$2_0_old))
                                    (INV_42_MAIN .0$1_0 r$1_0 x.0$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0)))))))))))))
; forbidden main
; offbyn main
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int)
       (.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13_MAIN .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old)
         (let
            ((_$1_10 (> .01$1_0_old 0)))
            (=>
               _$1_10
               (let
                  ((_$1_14 (+ x.2$1_0_old 2))
                   (_$1_15 (+ .01$1_0_old (- 1))))
                  (let
                     ((.01$1_0 _$1_15)
                      (x.2$1_0 _$1_14))
                     (=>
                        (and
                           (let
                              ((_$2_11 (> .01$2_0_old 0)))
                              (=>
                                 _$2_11
                                 (let
                                    ((_$2_15 (+ x.2$2_0_old 2))
                                     (_$2_16 (+ .01$2_0_old (- 1))))
                                    (let
                                       ((.01$2_0 _$2_16)
                                        (x.2$2_0 _$2_15))
                                       false)))))
                        (INV_13_MAIN .01$1_0 x.2$1_0 .01$2_0_old x.2$2_0_old)))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ x.0$1_0_old 1))
                   (_$1_7 (+ .0$1_0_old (- 1))))
                  (let
                     ((.0$1_0 _$1_7)
                      (x.0$1_0 _$1_6)
                      (r$1_0 r$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_3 (< 0 .0$2_0_old)))
                              (=>
                                 _$2_3
                                 (let
                                    ((_$2_7 (< 0 t$2_0_old)))
                                    (=>
                                       _$2_7
                                       (let
                                          ((_$2_8 (+ x.0$2_0_old 1)))
                                          (let
                                             ((x.1$2_0 _$2_8)
                                              (_$2_9 (+ .0$2_0_old (- 1))))
                                             (let
                                                ((.0$2_0 _$2_9)
                                                 (x.0$2_0 x.1$2_0)
                                                 (r$2_0 r$2_0_old)
                                                 (t$2_0 t$2_0_old))
                                                false)))))))
                           (let
                              ((_$2_3 (< 0 .0$2_0_old)))
                              (=>
                                 _$2_3
                                 (let
                                    ((_$2_7 (< 0 t$2_0_old)))
                                    (=>
                                       (not _$2_7)
                                       (let
                                          ((x.1$2_0 x.0$2_0_old)
                                           (_$2_9 (+ .0$2_0_old (- 1))))
                                          (let
                                             ((.0$2_0 _$2_9)
                                              (x.0$2_0 x.1$2_0)
                                              (r$2_0 r$2_0_old)
                                              (t$2_0 t$2_0_old))
                                             false)))))))
                        (INV_42_MAIN .0$1_0 r$1_0 x.0$1_0 .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int)
       (.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13_MAIN .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old)
         (let
            ((_$2_11 (> .01$2_0_old 0)))
            (=>
               _$2_11
               (let
                  ((_$2_15 (+ x.2$2_0_old 2))
                   (_$2_16 (+ .01$2_0_old (- 1))))
                  (let
                     ((.01$2_0 _$2_16)
                      (x.2$2_0 _$2_15))
                     (=>
                        (and
                           (let
                              ((_$1_10 (> .01$1_0_old 0)))
                              (=>
                                 _$1_10
                                 (let
                                    ((_$1_14 (+ x.2$1_0_old 2))
                                     (_$1_15 (+ .01$1_0_old (- 1))))
                                    (let
                                       ((.01$1_0 _$1_15)
                                        (x.2$1_0 _$1_14))
                                       false)))))
                        (INV_13_MAIN .01$1_0_old x.2$1_0_old .01$2_0 x.2$2_0)))))))))
(assert
   (forall
      ((r$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_23_MAIN r$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     _$2_7
                     (let
                        ((_$2_8 (+ x.0$2_0_old 1)))
                        (let
                           ((x.1$2_0 _$2_8)
                            (_$2_9 (+ .0$2_0_old (- 1))))
                           (let
                              ((.0$2_0 _$2_9)
                               (x.0$2_0 x.1$2_0)
                               (r$2_0 r$2_0_old)
                               (t$2_0 t$2_0_old))
                              (INV_23_MAIN r$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0)))))))))))
(assert
   (forall
      ((r$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_23_MAIN r$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     (not _$2_7)
                     (let
                        ((x.1$2_0 x.0$2_0_old)
                         (_$2_9 (+ .0$2_0_old (- 1))))
                        (let
                           ((.0$2_0 _$2_9)
                            (x.0$2_0 x.1$2_0)
                            (r$2_0 r$2_0_old)
                            (t$2_0 t$2_0_old))
                           (INV_23_MAIN r$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     _$2_7
                     (let
                        ((_$2_8 (+ x.0$2_0_old 1)))
                        (let
                           ((x.1$2_0 _$2_8)
                            (_$2_9 (+ .0$2_0_old (- 1))))
                           (let
                              ((.0$2_0 _$2_9)
                               (x.0$2_0 x.1$2_0)
                               (r$2_0 r$2_0_old)
                               (t$2_0 t$2_0_old))
                              (=>
                                 (and
                                    (let
                                       ((_$1_2 (< 0 .0$1_0_old)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ x.0$1_0_old 1))
                                              (_$1_7 (+ .0$1_0_old (- 1))))
                                             (let
                                                ((.0$1_0 _$1_7)
                                                 (x.0$1_0 _$1_6)
                                                 (r$1_0 r$1_0_old))
                                                false)))))
                                 (INV_42_MAIN .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     (not _$2_7)
                     (let
                        ((x.1$2_0 x.0$2_0_old)
                         (_$2_9 (+ .0$2_0_old (- 1))))
                        (let
                           ((.0$2_0 _$2_9)
                            (x.0$2_0 x.1$2_0)
                            (r$2_0 r$2_0_old)
                            (t$2_0 t$2_0_old))
                           (=>
                              (and
                                 (let
                                    ((_$1_2 (< 0 .0$1_0_old)))
                                    (=>
                                       _$1_2
                                       (let
                                          ((_$1_6 (+ x.0$1_0_old 1))
                                           (_$1_7 (+ .0$1_0_old (- 1))))
                                          (let
                                             ((.0$1_0 _$1_7)
                                              (x.0$1_0 _$1_6)
                                              (r$1_0 r$1_0_old))
                                             false)))))
                              (INV_42_MAIN .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0)))))))))))
; end
(assert
   (forall
      ((t$1_0_old Int)
       (c$1_0_old Int)
       (r$1_0_old Int)
       (t$2_0_old Int)
       (c$2_0_old Int)
       (r$2_0_old Int))
      (=>
         (INV_REC_f_PRE t$1_0_old c$1_0_old r$1_0_old t$2_0_old c$2_0_old r$2_0_old)
         (let
            ((_$1_0 (< 0 t$1_0_old)))
            (=>
               (not _$1_0)
               (let
                  ((r$1_0 r$1_0_old)
                   (.0$2_0 c$2_0_old)
                   (x.0$2_0 0)
                   (r$2_0 r$2_0_old)
                   (t$2_0 t$2_0_old))
                  (forall
                     ((result$1 Int)
                      (result$2 Int))
                     (and
                        (INV_23_PRE r$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0)
                        (=>
                           (INV_23 r$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$1 result$2)
                           (INV_REC_f t$1_0_old c$1_0_old r$1_0_old t$2_0_old c$2_0_old r$2_0_old result$1 result$2))))))))))
(assert
   (forall
      ((t$1_0_old Int)
       (c$1_0_old Int)
       (r$1_0_old Int)
       (t$2_0_old Int)
       (c$2_0_old Int)
       (r$2_0_old Int))
      (=>
         (INV_REC_f_PRE t$1_0_old c$1_0_old r$1_0_old t$2_0_old c$2_0_old r$2_0_old)
         (let
            ((_$1_0 (< 0 t$1_0_old)))
            (=>
               _$1_0
               (let
                  ((.0$1_0 c$1_0_old)
                   (x.0$1_0 0)
                   (r$1_0 r$1_0_old)
                   (.0$2_0 c$2_0_old)
                   (x.0$2_0 0)
                   (r$2_0 r$2_0_old)
                   (t$2_0 t$2_0_old))
                  (forall
                     ((result$1 Int)
                      (result$2 Int))
                     (and
                        (INV_42_PRE .0$1_0 r$1_0 x.0$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0)
                        (=>
                           (INV_42 .0$1_0 r$1_0 x.0$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$1 result$2)
                           (INV_REC_f t$1_0_old c$1_0_old r$1_0_old t$2_0_old c$2_0_old r$2_0_old result$1 result$2))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int)
       (.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13_PRE .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old)
         (let
            ((_$1_10 (> .01$1_0_old 0)))
            (=>
               (not _$1_10)
               (let
                  ((result$1 x.2$1_0_old)
                   (_$2_11 (> .01$2_0_old 0)))
                  (=>
                     (not _$2_11)
                     (let
                        ((result$2 x.2$2_0_old))
                        (INV_13 .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old result$1 result$2)))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int)
       (.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13_PRE .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old)
         (let
            ((_$1_10 (> .01$1_0_old 0)))
            (=>
               _$1_10
               (let
                  ((_$1_14 (+ x.2$1_0_old 2))
                   (_$1_15 (+ .01$1_0_old (- 1))))
                  (let
                     ((.01$1_0 _$1_15)
                      (x.2$1_0 _$1_14)
                      (_$2_11 (> .01$2_0_old 0)))
                     (=>
                        _$2_11
                        (let
                           ((_$2_15 (+ x.2$2_0_old 2))
                            (_$2_16 (+ .01$2_0_old (- 1))))
                           (let
                              ((.01$2_0 _$2_16)
                               (x.2$2_0 _$2_15))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_13_PRE .01$1_0 x.2$1_0 .01$2_0 x.2$2_0)
                                    (=>
                                       (INV_13 .01$1_0 x.2$1_0 .01$2_0 x.2$2_0 result$1 result$2)
                                       (INV_13 .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((r$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_23_PRE r$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((x.1$1_0 0))
            (let
               ((.01$1_0 r$1_0_old)
                (x.2$1_0 x.1$1_0)
                (_$2_3 (< 0 .0$2_0_old)))
               (=>
                  (not _$2_3)
                  (let
                     ((.01$2_0 r$2_0_old)
                      (x.2$2_0 x.0$2_0_old))
                     (forall
                        ((result$1 Int)
                         (result$2 Int))
                        (and
                           (INV_13_PRE .01$1_0 x.2$1_0 .01$2_0 x.2$2_0)
                           (=>
                              (INV_13 .01$1_0 x.2$1_0 .01$2_0 x.2$2_0 result$1 result$2)
                              (INV_23 r$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               (not _$1_2)
               (let
                  ((x.1$1_0 x.0$1_0_old))
                  (let
                     ((.01$1_0 r$1_0_old)
                      (x.2$1_0 x.1$1_0)
                      (_$2_3 (< 0 .0$2_0_old)))
                     (=>
                        (not _$2_3)
                        (let
                           ((.01$2_0 r$2_0_old)
                            (x.2$2_0 x.0$2_0_old))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_13_PRE .01$1_0 x.2$1_0 .01$2_0 x.2$2_0)
                                 (=>
                                    (INV_13 .01$1_0 x.2$1_0 .01$2_0 x.2$2_0 result$1 result$2)
                                    (INV_42 .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ x.0$1_0_old 1))
                   (_$1_7 (+ .0$1_0_old (- 1))))
                  (let
                     ((.0$1_0 _$1_7)
                      (x.0$1_0 _$1_6)
                      (r$1_0 r$1_0_old)
                      (_$2_3 (< 0 .0$2_0_old)))
                     (=>
                        _$2_3
                        (let
                           ((_$2_7 (< 0 t$2_0_old)))
                           (=>
                              _$2_7
                              (let
                                 ((_$2_8 (+ x.0$2_0_old 1)))
                                 (let
                                    ((x.1$2_0 _$2_8)
                                     (_$2_9 (+ .0$2_0_old (- 1))))
                                    (let
                                       ((.0$2_0 _$2_9)
                                        (x.0$2_0 x.1$2_0)
                                        (r$2_0 r$2_0_old)
                                        (t$2_0 t$2_0_old))
                                       (forall
                                          ((result$1 Int)
                                           (result$2 Int))
                                          (and
                                             (INV_42_PRE .0$1_0 r$1_0 x.0$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0)
                                             (=>
                                                (INV_42 .0$1_0 r$1_0 x.0$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$1 result$2)
                                                (INV_42 .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ x.0$1_0_old 1))
                   (_$1_7 (+ .0$1_0_old (- 1))))
                  (let
                     ((.0$1_0 _$1_7)
                      (x.0$1_0 _$1_6)
                      (r$1_0 r$1_0_old)
                      (_$2_3 (< 0 .0$2_0_old)))
                     (=>
                        _$2_3
                        (let
                           ((_$2_7 (< 0 t$2_0_old)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((x.1$2_0 x.0$2_0_old)
                                  (_$2_9 (+ .0$2_0_old (- 1))))
                                 (let
                                    ((.0$2_0 _$2_9)
                                     (x.0$2_0 x.1$2_0)
                                     (r$2_0 r$2_0_old)
                                     (t$2_0 t$2_0_old))
                                    (forall
                                       ((result$1 Int)
                                        (result$2 Int))
                                       (and
                                          (INV_42_PRE .0$1_0 r$1_0 x.0$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0)
                                          (=>
                                             (INV_42 .0$1_0 r$1_0 x.0$1_0 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$1 result$2)
                                             (INV_42 .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((t$1_0_old Int)
       (c$1_0_old Int)
       (r$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE t$1_0_old c$1_0_old r$1_0_old)
         (let
            ((_$1_0 (< 0 t$1_0_old)))
            (=>
               (not _$1_0)
               (let
                  ((r$1_0 r$1_0_old))
                  (forall
                     ((result$1 Int))
                     (=>
                        (INV_23__1 r$1_0 result$1)
                        (INV_REC_f__1 t$1_0_old c$1_0_old r$1_0_old result$1)))))))))
(assert
   (forall
      ((t$1_0_old Int)
       (c$1_0_old Int)
       (r$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE t$1_0_old c$1_0_old r$1_0_old)
         (let
            ((_$1_0 (< 0 t$1_0_old)))
            (=>
               _$1_0
               (let
                  ((.0$1_0 c$1_0_old)
                   (x.0$1_0 0)
                   (r$1_0 r$1_0_old))
                  (forall
                     ((result$1 Int))
                     (=>
                        (INV_42__1 .0$1_0 r$1_0 x.0$1_0 result$1)
                        (INV_REC_f__1 t$1_0_old c$1_0_old r$1_0_old result$1)))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int))
      (=>
         (INV_13__1_PRE .01$1_0_old x.2$1_0_old)
         (let
            ((_$1_10 (> .01$1_0_old 0)))
            (=>
               (not _$1_10)
               (let
                  ((result$1 x.2$1_0_old))
                  (INV_13__1 .01$1_0_old x.2$1_0_old result$1)))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int))
      (=>
         (INV_13__1_PRE .01$1_0_old x.2$1_0_old)
         (let
            ((_$1_10 (> .01$1_0_old 0)))
            (=>
               _$1_10
               (let
                  ((_$1_14 (+ x.2$1_0_old 2))
                   (_$1_15 (+ .01$1_0_old (- 1))))
                  (let
                     ((.01$1_0 _$1_15)
                      (x.2$1_0 _$1_14))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_13__1 .01$1_0 x.2$1_0 result$1)
                           (INV_13__1 .01$1_0_old x.2$1_0_old result$1))))))))))
(assert
   (forall
      ((r$1_0_old Int))
      (=>
         (INV_23__1_PRE r$1_0_old)
         (let
            ((x.1$1_0 0))
            (let
               ((.01$1_0 r$1_0_old)
                (x.2$1_0 x.1$1_0))
               (forall
                  ((result$1 Int))
                  (=>
                     (INV_13__1 .01$1_0 x.2$1_0 result$1)
                     (INV_23__1 r$1_0_old result$1))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int))
      (=>
         (INV_42__1_PRE .0$1_0_old r$1_0_old x.0$1_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               (not _$1_2)
               (let
                  ((x.1$1_0 x.0$1_0_old))
                  (let
                     ((.01$1_0 r$1_0_old)
                      (x.2$1_0 x.1$1_0))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_13__1 .01$1_0 x.2$1_0 result$1)
                           (INV_42__1 .0$1_0_old r$1_0_old x.0$1_0_old result$1))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int))
      (=>
         (INV_42__1_PRE .0$1_0_old r$1_0_old x.0$1_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ x.0$1_0_old 1))
                   (_$1_7 (+ .0$1_0_old (- 1))))
                  (let
                     ((.0$1_0 _$1_7)
                      (x.0$1_0 _$1_6)
                      (r$1_0 r$1_0_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_42__1 .0$1_0 r$1_0 x.0$1_0 result$1)
                           (INV_42__1 .0$1_0_old r$1_0_old x.0$1_0_old result$1))))))))))
(assert
   (forall
      ((t$2_0_old Int)
       (c$2_0_old Int)
       (r$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE t$2_0_old c$2_0_old r$2_0_old)
         (let
            ((.0$2_0 c$2_0_old)
             (x.0$2_0 0)
             (r$2_0 r$2_0_old)
             (t$2_0 t$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_23__2 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$2)
                  (INV_REC_f__2 t$2_0_old c$2_0_old r$2_0_old result$2)))))))
(assert
   (forall
      ((t$2_0_old Int)
       (c$2_0_old Int)
       (r$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE t$2_0_old c$2_0_old r$2_0_old)
         (let
            ((.0$2_0 c$2_0_old)
             (x.0$2_0 0)
             (r$2_0 r$2_0_old)
             (t$2_0 t$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_42__2 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$2)
                  (INV_REC_f__2 t$2_0_old c$2_0_old r$2_0_old result$2)))))))
(assert
   (forall
      ((.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13__2_PRE .01$2_0_old x.2$2_0_old)
         (let
            ((_$2_11 (> .01$2_0_old 0)))
            (=>
               (not _$2_11)
               (let
                  ((result$2 x.2$2_0_old))
                  (INV_13__2 .01$2_0_old x.2$2_0_old result$2)))))))
(assert
   (forall
      ((.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13__2_PRE .01$2_0_old x.2$2_0_old)
         (let
            ((_$2_11 (> .01$2_0_old 0)))
            (=>
               _$2_11
               (let
                  ((_$2_15 (+ x.2$2_0_old 2))
                   (_$2_16 (+ .01$2_0_old (- 1))))
                  (let
                     ((.01$2_0 _$2_16)
                      (x.2$2_0 _$2_15))
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_13__2 .01$2_0 x.2$2_0 result$2)
                           (INV_13__2 .01$2_0_old x.2$2_0_old result$2))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_23__2_PRE .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               (not _$2_3)
               (let
                  ((.01$2_0 r$2_0_old)
                   (x.2$2_0 x.0$2_0_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_13__2 .01$2_0 x.2$2_0 result$2)
                        (INV_23__2 .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$2)))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_23__2_PRE .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     _$2_7
                     (let
                        ((_$2_8 (+ x.0$2_0_old 1)))
                        (let
                           ((x.1$2_0 _$2_8)
                            (_$2_9 (+ .0$2_0_old (- 1))))
                           (let
                              ((.0$2_0 _$2_9)
                               (x.0$2_0 x.1$2_0)
                               (r$2_0 r$2_0_old)
                               (t$2_0 t$2_0_old))
                              (forall
                                 ((result$2 Int))
                                 (=>
                                    (INV_23__2 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$2)
                                    (INV_23__2 .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$2)))))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_23__2_PRE .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     (not _$2_7)
                     (let
                        ((x.1$2_0 x.0$2_0_old)
                         (_$2_9 (+ .0$2_0_old (- 1))))
                        (let
                           ((.0$2_0 _$2_9)
                            (x.0$2_0 x.1$2_0)
                            (r$2_0 r$2_0_old)
                            (t$2_0 t$2_0_old))
                           (forall
                              ((result$2 Int))
                              (=>
                                 (INV_23__2 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$2)
                                 (INV_23__2 .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$2))))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               (not _$2_3)
               (let
                  ((.01$2_0 r$2_0_old)
                   (x.2$2_0 x.0$2_0_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_13__2 .01$2_0 x.2$2_0 result$2)
                        (INV_42__2 .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$2)))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     _$2_7
                     (let
                        ((_$2_8 (+ x.0$2_0_old 1)))
                        (let
                           ((x.1$2_0 _$2_8)
                            (_$2_9 (+ .0$2_0_old (- 1))))
                           (let
                              ((.0$2_0 _$2_9)
                               (x.0$2_0 x.1$2_0)
                               (r$2_0 r$2_0_old)
                               (t$2_0 t$2_0_old))
                              (forall
                                 ((result$2 Int))
                                 (=>
                                    (INV_42__2 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$2)
                                    (INV_42__2 .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$2)))))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     (not _$2_7)
                     (let
                        ((x.1$2_0 x.0$2_0_old)
                         (_$2_9 (+ .0$2_0_old (- 1))))
                        (let
                           ((.0$2_0 _$2_9)
                            (x.0$2_0 x.1$2_0)
                            (r$2_0 r$2_0_old)
                            (t$2_0 t$2_0_old))
                           (forall
                              ((result$2 Int))
                              (=>
                                 (INV_42__2 .0$2_0 r$2_0 t$2_0 x.0$2_0 result$2)
                                 (INV_42__2 .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$2))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int)
       (.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13_PRE .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old)
         (let
            ((_$1_10 (> .01$1_0_old 0)))
            (=>
               _$1_10
               (let
                  ((_$1_14 (+ x.2$1_0_old 2))
                   (_$1_15 (+ .01$1_0_old (- 1))))
                  (let
                     ((.01$1_0 _$1_15)
                      (x.2$1_0 _$1_14))
                     (=>
                        (and
                           (let
                              ((_$2_11 (> .01$2_0_old 0)))
                              (=>
                                 _$2_11
                                 (let
                                    ((_$2_15 (+ x.2$2_0_old 2))
                                     (_$2_16 (+ .01$2_0_old (- 1))))
                                    (let
                                       ((.01$2_0 _$2_16)
                                        (x.2$2_0 _$2_15))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_13_PRE .01$1_0 x.2$1_0 .01$2_0_old x.2$2_0_old)
                              (=>
                                 (INV_13 .01$1_0 x.2$1_0 .01$2_0_old x.2$2_0_old result$1 result$2)
                                 (INV_13 .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$1_2 (< 0 .0$1_0_old)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ x.0$1_0_old 1))
                   (_$1_7 (+ .0$1_0_old (- 1))))
                  (let
                     ((.0$1_0 _$1_7)
                      (x.0$1_0 _$1_6)
                      (r$1_0 r$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_3 (< 0 .0$2_0_old)))
                              (=>
                                 _$2_3
                                 (let
                                    ((_$2_7 (< 0 t$2_0_old)))
                                    (=>
                                       _$2_7
                                       (let
                                          ((_$2_8 (+ x.0$2_0_old 1)))
                                          (let
                                             ((x.1$2_0 _$2_8)
                                              (_$2_9 (+ .0$2_0_old (- 1))))
                                             (let
                                                ((.0$2_0 _$2_9)
                                                 (x.0$2_0 x.1$2_0)
                                                 (r$2_0 r$2_0_old)
                                                 (t$2_0 t$2_0_old))
                                                false)))))))
                           (let
                              ((_$2_3 (< 0 .0$2_0_old)))
                              (=>
                                 _$2_3
                                 (let
                                    ((_$2_7 (< 0 t$2_0_old)))
                                    (=>
                                       (not _$2_7)
                                       (let
                                          ((x.1$2_0 x.0$2_0_old)
                                           (_$2_9 (+ .0$2_0_old (- 1))))
                                          (let
                                             ((.0$2_0 _$2_9)
                                              (x.0$2_0 x.1$2_0)
                                              (r$2_0 r$2_0_old)
                                              (t$2_0 t$2_0_old))
                                             false)))))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_42_PRE .0$1_0 r$1_0 x.0$1_0 .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
                              (=>
                                 (INV_42 .0$1_0 r$1_0 x.0$1_0 .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2)
                                 (INV_42 .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (x.2$1_0_old Int)
       (.01$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_13_PRE .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old)
         (let
            ((_$2_11 (> .01$2_0_old 0)))
            (=>
               _$2_11
               (let
                  ((_$2_15 (+ x.2$2_0_old 2))
                   (_$2_16 (+ .01$2_0_old (- 1))))
                  (let
                     ((.01$2_0 _$2_16)
                      (x.2$2_0 _$2_15))
                     (=>
                        (and
                           (let
                              ((_$1_10 (> .01$1_0_old 0)))
                              (=>
                                 _$1_10
                                 (let
                                    ((_$1_14 (+ x.2$1_0_old 2))
                                     (_$1_15 (+ .01$1_0_old (- 1))))
                                    (let
                                       ((.01$1_0 _$1_15)
                                        (x.2$1_0 _$1_14))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_13_PRE .01$1_0_old x.2$1_0_old .01$2_0 x.2$2_0)
                              (=>
                                 (INV_13 .01$1_0_old x.2$1_0_old .01$2_0 x.2$2_0 result$1 result$2)
                                 (INV_13 .01$1_0_old x.2$1_0_old .01$2_0_old x.2$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((r$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_23_PRE r$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     _$2_7
                     (let
                        ((_$2_8 (+ x.0$2_0_old 1)))
                        (let
                           ((x.1$2_0 _$2_8)
                            (_$2_9 (+ .0$2_0_old (- 1))))
                           (let
                              ((.0$2_0 _$2_9)
                               (x.0$2_0 x.1$2_0)
                               (r$2_0 r$2_0_old)
                               (t$2_0 t$2_0_old))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_23_PRE r$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0)
                                    (=>
                                       (INV_23 r$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0 result$1 result$2)
                                       (INV_23 r$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((r$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_23_PRE r$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     (not _$2_7)
                     (let
                        ((x.1$2_0 x.0$2_0_old)
                         (_$2_9 (+ .0$2_0_old (- 1))))
                        (let
                           ((.0$2_0 _$2_9)
                            (x.0$2_0 x.1$2_0)
                            (r$2_0 r$2_0_old)
                            (t$2_0 t$2_0_old))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_23_PRE r$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0)
                                 (=>
                                    (INV_23 r$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0 result$1 result$2)
                                    (INV_23 r$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     _$2_7
                     (let
                        ((_$2_8 (+ x.0$2_0_old 1)))
                        (let
                           ((x.1$2_0 _$2_8)
                            (_$2_9 (+ .0$2_0_old (- 1))))
                           (let
                              ((.0$2_0 _$2_9)
                               (x.0$2_0 x.1$2_0)
                               (r$2_0 r$2_0_old)
                               (t$2_0 t$2_0_old))
                              (=>
                                 (and
                                    (let
                                       ((_$1_2 (< 0 .0$1_0_old)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ x.0$1_0_old 1))
                                              (_$1_7 (+ .0$1_0_old (- 1))))
                                             (let
                                                ((.0$1_0 _$1_7)
                                                 (x.0$1_0 _$1_6)
                                                 (r$1_0 r$1_0_old))
                                                false)))))
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_42_PRE .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0)
                                       (=>
                                          (INV_42 .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0 result$1 result$2)
                                          (INV_42 .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (r$1_0_old Int)
       (x.0$1_0_old Int)
       (.0$2_0_old Int)
       (r$2_0_old Int)
       (t$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old)
         (let
            ((_$2_3 (< 0 .0$2_0_old)))
            (=>
               _$2_3
               (let
                  ((_$2_7 (< 0 t$2_0_old)))
                  (=>
                     (not _$2_7)
                     (let
                        ((x.1$2_0 x.0$2_0_old)
                         (_$2_9 (+ .0$2_0_old (- 1))))
                        (let
                           ((.0$2_0 _$2_9)
                            (x.0$2_0 x.1$2_0)
                            (r$2_0 r$2_0_old)
                            (t$2_0 t$2_0_old))
                           (=>
                              (and
                                 (let
                                    ((_$1_2 (< 0 .0$1_0_old)))
                                    (=>
                                       _$1_2
                                       (let
                                          ((_$1_6 (+ x.0$1_0_old 1))
                                           (_$1_7 (+ .0$1_0_old (- 1))))
                                          (let
                                             ((.0$1_0 _$1_7)
                                              (x.0$1_0 _$1_6)
                                              (r$1_0 r$1_0_old))
                                             false)))))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_42_PRE .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0)
                                    (=>
                                       (INV_42 .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0 r$2_0 t$2_0 x.0$2_0 result$1 result$2)
                                       (INV_42 .0$1_0_old r$1_0_old x.0$1_0_old .0$2_0_old r$2_0_old t$2_0_old x.0$2_0_old result$1 result$2))))))))))))))
(check-sat)
(get-model)
