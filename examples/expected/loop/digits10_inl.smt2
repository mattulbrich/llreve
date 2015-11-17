(set-logic HORN)
(declare-fun
   INV_42_MAIN
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
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (and
            (= n$1_0_old n$2_0_old))
         (let
            ((_$1_0 (div
                n$1_0_old
                10)))
            (let
               ((result.0$1_0 1)
                (.0$1_0 _$1_0)
                (retval.0$2_0 (- 1))
                (b.0$2_0 1)
                (result.0$2_0 1)
                (.0$2_0 n$2_0_old))
               (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               (not _$1_2)
               (let
                  ((result$1 result.0$1_0_old)
                   (_$2_1 (= b.0$2_0_old 0)))
                  (let
                     ((_$2_2 (xor
                         _$2_1
                         true)))
                     (=>
                        (not _$2_2)
                        (let
                           ((result$2 retval.0$2_0_old))
                           (= result$1 result$2))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     _$2_6
                                                                     (let
                                                                        ((retval.4$2_0 result.0$2_0_old)
                                                                         (b.4$2_0 0)
                                                                         (result.4$2_0 result.0$2_0_old)
                                                                         (.4$2_0 .0$2_0_old))
                                                                        (let
                                                                           ((retval.0$2_0 retval.4$2_0)
                                                                            (b.0$2_0 b.4$2_0)
                                                                            (result.0$2_0 result.4$2_0)
                                                                            (.0$2_0 .4$2_0))
                                                                           (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     (not _$2_6)
                                                                     (let
                                                                        ((_$2_7 (< .0$2_0_old 100)))
                                                                        (=>
                                                                           _$2_7
                                                                           (let
                                                                              ((_$2_8 (+ result.0$2_0_old 1)))
                                                                              (let
                                                                                 ((retval.3$2_0 _$2_8)
                                                                                  (b.3$2_0 0)
                                                                                  (result.3$2_0 result.0$2_0_old)
                                                                                  (.3$2_0 .0$2_0_old))
                                                                                 (let
                                                                                    ((retval.4$2_0 retval.3$2_0)
                                                                                     (b.4$2_0 b.3$2_0)
                                                                                     (result.4$2_0 result.3$2_0)
                                                                                     (.4$2_0 .3$2_0))
                                                                                    (let
                                                                                       ((retval.0$2_0 retval.4$2_0)
                                                                                        (b.0$2_0 b.4$2_0)
                                                                                        (result.0$2_0 result.4$2_0)
                                                                                        (.0$2_0 .4$2_0))
                                                                                       (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     (not _$2_6)
                                                                     (let
                                                                        ((_$2_7 (< .0$2_0_old 100)))
                                                                        (=>
                                                                           (not _$2_7)
                                                                           (let
                                                                              ((_$2_9 (< .0$2_0_old 1000)))
                                                                              (=>
                                                                                 _$2_9
                                                                                 (let
                                                                                    ((_$2_10 (+ result.0$2_0_old 2)))
                                                                                    (let
                                                                                       ((retval.2$2_0 _$2_10)
                                                                                        (b.2$2_0 0)
                                                                                        (result.2$2_0 result.0$2_0_old)
                                                                                        (.2$2_0 .0$2_0_old))
                                                                                       (let
                                                                                          ((retval.3$2_0 retval.2$2_0)
                                                                                           (b.3$2_0 b.2$2_0)
                                                                                           (result.3$2_0 result.2$2_0)
                                                                                           (.3$2_0 .2$2_0))
                                                                                          (let
                                                                                             ((retval.4$2_0 retval.3$2_0)
                                                                                              (b.4$2_0 b.3$2_0)
                                                                                              (result.4$2_0 result.3$2_0)
                                                                                              (.4$2_0 .3$2_0))
                                                                                             (let
                                                                                                ((retval.0$2_0 retval.4$2_0)
                                                                                                 (b.0$2_0 b.4$2_0)
                                                                                                 (result.0$2_0 result.4$2_0)
                                                                                                 (.0$2_0 .4$2_0))
                                                                                                (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     (not _$2_6)
                                                                     (let
                                                                        ((_$2_7 (< .0$2_0_old 100)))
                                                                        (=>
                                                                           (not _$2_7)
                                                                           (let
                                                                              ((_$2_9 (< .0$2_0_old 1000)))
                                                                              (=>
                                                                                 (not _$2_9)
                                                                                 (let
                                                                                    ((_$2_11 (< .0$2_0_old 10000)))
                                                                                    (=>
                                                                                       _$2_11
                                                                                       (let
                                                                                          ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                          (let
                                                                                             ((retval.1$2_0 _$2_12)
                                                                                              (b.1$2_0 0)
                                                                                              (result.1$2_0 result.0$2_0_old)
                                                                                              (.1$2_0 .0$2_0_old))
                                                                                             (let
                                                                                                ((retval.2$2_0 retval.1$2_0)
                                                                                                 (b.2$2_0 b.1$2_0)
                                                                                                 (result.2$2_0 result.1$2_0)
                                                                                                 (.2$2_0 .1$2_0))
                                                                                                (let
                                                                                                   ((retval.3$2_0 retval.2$2_0)
                                                                                                    (b.3$2_0 b.2$2_0)
                                                                                                    (result.3$2_0 result.2$2_0)
                                                                                                    (.3$2_0 .2$2_0))
                                                                                                   (let
                                                                                                      ((retval.4$2_0 retval.3$2_0)
                                                                                                       (b.4$2_0 b.3$2_0)
                                                                                                       (result.4$2_0 result.3$2_0)
                                                                                                       (.4$2_0 .3$2_0))
                                                                                                      (let
                                                                                                         ((retval.0$2_0 retval.4$2_0)
                                                                                                          (b.0$2_0 b.4$2_0)
                                                                                                          (result.0$2_0 result.4$2_0)
                                                                                                          (.0$2_0 .4$2_0))
                                                                                                         (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     (not _$2_6)
                                                                     (let
                                                                        ((_$2_7 (< .0$2_0_old 100)))
                                                                        (=>
                                                                           (not _$2_7)
                                                                           (let
                                                                              ((_$2_9 (< .0$2_0_old 1000)))
                                                                              (=>
                                                                                 (not _$2_9)
                                                                                 (let
                                                                                    ((_$2_11 (< .0$2_0_old 10000)))
                                                                                    (=>
                                                                                       (not _$2_11)
                                                                                       (let
                                                                                          ((_$2_13 (div
                                                                                              .0$2_0_old
                                                                                              10000))
                                                                                           (_$2_14 (+ result.0$2_0_old 4)))
                                                                                          (let
                                                                                             ((retval.1$2_0 retval.0$2_0_old)
                                                                                              (b.1$2_0 b.0$2_0_old)
                                                                                              (result.1$2_0 _$2_14)
                                                                                              (.1$2_0 _$2_13))
                                                                                             (let
                                                                                                ((retval.2$2_0 retval.1$2_0)
                                                                                                 (b.2$2_0 b.1$2_0)
                                                                                                 (result.2$2_0 result.1$2_0)
                                                                                                 (.2$2_0 .1$2_0))
                                                                                                (let
                                                                                                   ((retval.3$2_0 retval.2$2_0)
                                                                                                    (b.3$2_0 b.2$2_0)
                                                                                                    (result.3$2_0 result.2$2_0)
                                                                                                    (.3$2_0 .2$2_0))
                                                                                                   (let
                                                                                                      ((retval.4$2_0 retval.3$2_0)
                                                                                                       (b.4$2_0 b.3$2_0)
                                                                                                       (result.4$2_0 result.3$2_0)
                                                                                                       (.4$2_0 .3$2_0))
                                                                                                      (let
                                                                                                         ((retval.0$2_0 retval.4$2_0)
                                                                                                          (b.0$2_0 b.4$2_0)
                                                                                                          (result.0$2_0 result.4$2_0)
                                                                                                          (.0$2_0 .4$2_0))
                                                                                                         (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  _$2_6
                                                                  (let
                                                                     ((retval.4$2_0 result.0$2_0_old)
                                                                      (b.4$2_0 0)
                                                                      (result.4$2_0 result.0$2_0_old)
                                                                      (.4$2_0 .0$2_0_old))
                                                                     (let
                                                                        ((retval.0$2_0 retval.4$2_0)
                                                                         (b.0$2_0 b.4$2_0)
                                                                         (result.0$2_0 result.4$2_0)
                                                                         (.0$2_0 .4$2_0))
                                                                        (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  (not _$2_6)
                                                                  (let
                                                                     ((_$2_7 (< .0$2_0_old 100)))
                                                                     (=>
                                                                        _$2_7
                                                                        (let
                                                                           ((_$2_8 (+ result.0$2_0_old 1)))
                                                                           (let
                                                                              ((retval.3$2_0 _$2_8)
                                                                               (b.3$2_0 0)
                                                                               (result.3$2_0 result.0$2_0_old)
                                                                               (.3$2_0 .0$2_0_old))
                                                                              (let
                                                                                 ((retval.4$2_0 retval.3$2_0)
                                                                                  (b.4$2_0 b.3$2_0)
                                                                                  (result.4$2_0 result.3$2_0)
                                                                                  (.4$2_0 .3$2_0))
                                                                                 (let
                                                                                    ((retval.0$2_0 retval.4$2_0)
                                                                                     (b.0$2_0 b.4$2_0)
                                                                                     (result.0$2_0 result.4$2_0)
                                                                                     (.0$2_0 .4$2_0))
                                                                                    (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  (not _$2_6)
                                                                  (let
                                                                     ((_$2_7 (< .0$2_0_old 100)))
                                                                     (=>
                                                                        (not _$2_7)
                                                                        (let
                                                                           ((_$2_9 (< .0$2_0_old 1000)))
                                                                           (=>
                                                                              _$2_9
                                                                              (let
                                                                                 ((_$2_10 (+ result.0$2_0_old 2)))
                                                                                 (let
                                                                                    ((retval.2$2_0 _$2_10)
                                                                                     (b.2$2_0 0)
                                                                                     (result.2$2_0 result.0$2_0_old)
                                                                                     (.2$2_0 .0$2_0_old))
                                                                                    (let
                                                                                       ((retval.3$2_0 retval.2$2_0)
                                                                                        (b.3$2_0 b.2$2_0)
                                                                                        (result.3$2_0 result.2$2_0)
                                                                                        (.3$2_0 .2$2_0))
                                                                                       (let
                                                                                          ((retval.4$2_0 retval.3$2_0)
                                                                                           (b.4$2_0 b.3$2_0)
                                                                                           (result.4$2_0 result.3$2_0)
                                                                                           (.4$2_0 .3$2_0))
                                                                                          (let
                                                                                             ((retval.0$2_0 retval.4$2_0)
                                                                                              (b.0$2_0 b.4$2_0)
                                                                                              (result.0$2_0 result.4$2_0)
                                                                                              (.0$2_0 .4$2_0))
                                                                                             (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  (not _$2_6)
                                                                  (let
                                                                     ((_$2_7 (< .0$2_0_old 100)))
                                                                     (=>
                                                                        (not _$2_7)
                                                                        (let
                                                                           ((_$2_9 (< .0$2_0_old 1000)))
                                                                           (=>
                                                                              (not _$2_9)
                                                                              (let
                                                                                 ((_$2_11 (< .0$2_0_old 10000)))
                                                                                 (=>
                                                                                    _$2_11
                                                                                    (let
                                                                                       ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                       (let
                                                                                          ((retval.1$2_0 _$2_12)
                                                                                           (b.1$2_0 0)
                                                                                           (result.1$2_0 result.0$2_0_old)
                                                                                           (.1$2_0 .0$2_0_old))
                                                                                          (let
                                                                                             ((retval.2$2_0 retval.1$2_0)
                                                                                              (b.2$2_0 b.1$2_0)
                                                                                              (result.2$2_0 result.1$2_0)
                                                                                              (.2$2_0 .1$2_0))
                                                                                             (let
                                                                                                ((retval.3$2_0 retval.2$2_0)
                                                                                                 (b.3$2_0 b.2$2_0)
                                                                                                 (result.3$2_0 result.2$2_0)
                                                                                                 (.3$2_0 .2$2_0))
                                                                                                (let
                                                                                                   ((retval.4$2_0 retval.3$2_0)
                                                                                                    (b.4$2_0 b.3$2_0)
                                                                                                    (result.4$2_0 result.3$2_0)
                                                                                                    (.4$2_0 .3$2_0))
                                                                                                   (let
                                                                                                      ((retval.0$2_0 retval.4$2_0)
                                                                                                       (b.0$2_0 b.4$2_0)
                                                                                                       (result.0$2_0 result.4$2_0)
                                                                                                       (.0$2_0 .4$2_0))
                                                                                                      (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  (not _$2_6)
                                                                  (let
                                                                     ((_$2_7 (< .0$2_0_old 100)))
                                                                     (=>
                                                                        (not _$2_7)
                                                                        (let
                                                                           ((_$2_9 (< .0$2_0_old 1000)))
                                                                           (=>
                                                                              (not _$2_9)
                                                                              (let
                                                                                 ((_$2_11 (< .0$2_0_old 10000)))
                                                                                 (=>
                                                                                    (not _$2_11)
                                                                                    (let
                                                                                       ((_$2_13 (div
                                                                                           .0$2_0_old
                                                                                           10000))
                                                                                        (_$2_14 (+ result.0$2_0_old 4)))
                                                                                       (let
                                                                                          ((retval.1$2_0 retval.0$2_0_old)
                                                                                           (b.1$2_0 b.0$2_0_old)
                                                                                           (result.1$2_0 _$2_14)
                                                                                           (.1$2_0 _$2_13))
                                                                                          (let
                                                                                             ((retval.2$2_0 retval.1$2_0)
                                                                                              (b.2$2_0 b.1$2_0)
                                                                                              (result.2$2_0 result.1$2_0)
                                                                                              (.2$2_0 .1$2_0))
                                                                                             (let
                                                                                                ((retval.3$2_0 retval.2$2_0)
                                                                                                 (b.3$2_0 b.2$2_0)
                                                                                                 (result.3$2_0 result.2$2_0)
                                                                                                 (.3$2_0 .2$2_0))
                                                                                                (let
                                                                                                   ((retval.4$2_0 retval.3$2_0)
                                                                                                    (b.4$2_0 b.3$2_0)
                                                                                                    (result.4$2_0 result.3$2_0)
                                                                                                    (.4$2_0 .3$2_0))
                                                                                                   (let
                                                                                                      ((retval.0$2_0 retval.4$2_0)
                                                                                                       (b.0$2_0 b.4$2_0)
                                                                                                       (result.0$2_0 result.4$2_0)
                                                                                                       (.0$2_0 .4$2_0))
                                                                                                      (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      _$2_6
                                                      (let
                                                         ((retval.4$2_0 result.0$2_0_old)
                                                          (b.4$2_0 0)
                                                          (result.4$2_0 result.0$2_0_old)
                                                          (.4$2_0 .0$2_0_old))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      (not _$2_6)
                                                      (let
                                                         ((_$2_7 (< .0$2_0_old 100)))
                                                         (=>
                                                            _$2_7
                                                            (let
                                                               ((_$2_8 (+ result.0$2_0_old 1)))
                                                               (let
                                                                  ((retval.3$2_0 _$2_8)
                                                                   (b.3$2_0 0)
                                                                   (result.3$2_0 result.0$2_0_old)
                                                                   (.3$2_0 .0$2_0_old))
                                                                  (let
                                                                     ((retval.4$2_0 retval.3$2_0)
                                                                      (b.4$2_0 b.3$2_0)
                                                                      (result.4$2_0 result.3$2_0)
                                                                      (.4$2_0 .3$2_0))
                                                                     (let
                                                                        ((retval.0$2_0 retval.4$2_0)
                                                                         (b.0$2_0 b.4$2_0)
                                                                         (result.0$2_0 result.4$2_0)
                                                                         (.0$2_0 .4$2_0))
                                                                        (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      (not _$2_6)
                                                      (let
                                                         ((_$2_7 (< .0$2_0_old 100)))
                                                         (=>
                                                            (not _$2_7)
                                                            (let
                                                               ((_$2_9 (< .0$2_0_old 1000)))
                                                               (=>
                                                                  _$2_9
                                                                  (let
                                                                     ((_$2_10 (+ result.0$2_0_old 2)))
                                                                     (let
                                                                        ((retval.2$2_0 _$2_10)
                                                                         (b.2$2_0 0)
                                                                         (result.2$2_0 result.0$2_0_old)
                                                                         (.2$2_0 .0$2_0_old))
                                                                        (let
                                                                           ((retval.3$2_0 retval.2$2_0)
                                                                            (b.3$2_0 b.2$2_0)
                                                                            (result.3$2_0 result.2$2_0)
                                                                            (.3$2_0 .2$2_0))
                                                                           (let
                                                                              ((retval.4$2_0 retval.3$2_0)
                                                                               (b.4$2_0 b.3$2_0)
                                                                               (result.4$2_0 result.3$2_0)
                                                                               (.4$2_0 .3$2_0))
                                                                              (let
                                                                                 ((retval.0$2_0 retval.4$2_0)
                                                                                  (b.0$2_0 b.4$2_0)
                                                                                  (result.0$2_0 result.4$2_0)
                                                                                  (.0$2_0 .4$2_0))
                                                                                 (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      (not _$2_6)
                                                      (let
                                                         ((_$2_7 (< .0$2_0_old 100)))
                                                         (=>
                                                            (not _$2_7)
                                                            (let
                                                               ((_$2_9 (< .0$2_0_old 1000)))
                                                               (=>
                                                                  (not _$2_9)
                                                                  (let
                                                                     ((_$2_11 (< .0$2_0_old 10000)))
                                                                     (=>
                                                                        _$2_11
                                                                        (let
                                                                           ((_$2_12 (+ result.0$2_0_old 3)))
                                                                           (let
                                                                              ((retval.1$2_0 _$2_12)
                                                                               (b.1$2_0 0)
                                                                               (result.1$2_0 result.0$2_0_old)
                                                                               (.1$2_0 .0$2_0_old))
                                                                              (let
                                                                                 ((retval.2$2_0 retval.1$2_0)
                                                                                  (b.2$2_0 b.1$2_0)
                                                                                  (result.2$2_0 result.1$2_0)
                                                                                  (.2$2_0 .1$2_0))
                                                                                 (let
                                                                                    ((retval.3$2_0 retval.2$2_0)
                                                                                     (b.3$2_0 b.2$2_0)
                                                                                     (result.3$2_0 result.2$2_0)
                                                                                     (.3$2_0 .2$2_0))
                                                                                    (let
                                                                                       ((retval.4$2_0 retval.3$2_0)
                                                                                        (b.4$2_0 b.3$2_0)
                                                                                        (result.4$2_0 result.3$2_0)
                                                                                        (.4$2_0 .3$2_0))
                                                                                       (let
                                                                                          ((retval.0$2_0 retval.4$2_0)
                                                                                           (b.0$2_0 b.4$2_0)
                                                                                           (result.0$2_0 result.4$2_0)
                                                                                           (.0$2_0 .4$2_0))
                                                                                          (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      (not _$2_6)
                                                      (let
                                                         ((_$2_7 (< .0$2_0_old 100)))
                                                         (=>
                                                            (not _$2_7)
                                                            (let
                                                               ((_$2_9 (< .0$2_0_old 1000)))
                                                               (=>
                                                                  (not _$2_9)
                                                                  (let
                                                                     ((_$2_11 (< .0$2_0_old 10000)))
                                                                     (=>
                                                                        (not _$2_11)
                                                                        (let
                                                                           ((_$2_13 (div
                                                                               .0$2_0_old
                                                                               10000))
                                                                            (_$2_14 (+ result.0$2_0_old 4)))
                                                                           (let
                                                                              ((retval.1$2_0 retval.0$2_0_old)
                                                                               (b.1$2_0 b.0$2_0_old)
                                                                               (result.1$2_0 _$2_14)
                                                                               (.1$2_0 _$2_13))
                                                                              (let
                                                                                 ((retval.2$2_0 retval.1$2_0)
                                                                                  (b.2$2_0 b.1$2_0)
                                                                                  (result.2$2_0 result.1$2_0)
                                                                                  (.2$2_0 .1$2_0))
                                                                                 (let
                                                                                    ((retval.3$2_0 retval.2$2_0)
                                                                                     (b.3$2_0 b.2$2_0)
                                                                                     (result.3$2_0 result.2$2_0)
                                                                                     (.3$2_0 .2$2_0))
                                                                                    (let
                                                                                       ((retval.4$2_0 retval.3$2_0)
                                                                                        (b.4$2_0 b.3$2_0)
                                                                                        (result.4$2_0 result.3$2_0)
                                                                                        (.4$2_0 .3$2_0))
                                                                                       (let
                                                                                          ((retval.0$2_0 retval.4$2_0)
                                                                                           (b.0$2_0 b.4$2_0)
                                                                                           (result.0$2_0 result.4$2_0)
                                                                                           (.0$2_0 .4$2_0))
                                                                                          (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          _$2_6
                                          (let
                                             ((retval.4$2_0 result.0$2_0_old)
                                              (b.4$2_0 0)
                                              (result.4$2_0 result.0$2_0_old)
                                              (.4$2_0 .0$2_0_old))
                                             (let
                                                ((retval.0$2_0 retval.4$2_0)
                                                 (b.0$2_0 b.4$2_0)
                                                 (result.0$2_0 result.4$2_0)
                                                 (.0$2_0 .4$2_0))
                                                (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          (not _$2_6)
                                          (let
                                             ((_$2_7 (< .0$2_0_old 100)))
                                             (=>
                                                _$2_7
                                                (let
                                                   ((_$2_8 (+ result.0$2_0_old 1)))
                                                   (let
                                                      ((retval.3$2_0 _$2_8)
                                                       (b.3$2_0 0)
                                                       (result.3$2_0 result.0$2_0_old)
                                                       (.3$2_0 .0$2_0_old))
                                                      (let
                                                         ((retval.4$2_0 retval.3$2_0)
                                                          (b.4$2_0 b.3$2_0)
                                                          (result.4$2_0 result.3$2_0)
                                                          (.4$2_0 .3$2_0))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          (not _$2_6)
                                          (let
                                             ((_$2_7 (< .0$2_0_old 100)))
                                             (=>
                                                (not _$2_7)
                                                (let
                                                   ((_$2_9 (< .0$2_0_old 1000)))
                                                   (=>
                                                      _$2_9
                                                      (let
                                                         ((_$2_10 (+ result.0$2_0_old 2)))
                                                         (let
                                                            ((retval.2$2_0 _$2_10)
                                                             (b.2$2_0 0)
                                                             (result.2$2_0 result.0$2_0_old)
                                                             (.2$2_0 .0$2_0_old))
                                                            (let
                                                               ((retval.3$2_0 retval.2$2_0)
                                                                (b.3$2_0 b.2$2_0)
                                                                (result.3$2_0 result.2$2_0)
                                                                (.3$2_0 .2$2_0))
                                                               (let
                                                                  ((retval.4$2_0 retval.3$2_0)
                                                                   (b.4$2_0 b.3$2_0)
                                                                   (result.4$2_0 result.3$2_0)
                                                                   (.4$2_0 .3$2_0))
                                                                  (let
                                                                     ((retval.0$2_0 retval.4$2_0)
                                                                      (b.0$2_0 b.4$2_0)
                                                                      (result.0$2_0 result.4$2_0)
                                                                      (.0$2_0 .4$2_0))
                                                                     (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          (not _$2_6)
                                          (let
                                             ((_$2_7 (< .0$2_0_old 100)))
                                             (=>
                                                (not _$2_7)
                                                (let
                                                   ((_$2_9 (< .0$2_0_old 1000)))
                                                   (=>
                                                      (not _$2_9)
                                                      (let
                                                         ((_$2_11 (< .0$2_0_old 10000)))
                                                         (=>
                                                            _$2_11
                                                            (let
                                                               ((_$2_12 (+ result.0$2_0_old 3)))
                                                               (let
                                                                  ((retval.1$2_0 _$2_12)
                                                                   (b.1$2_0 0)
                                                                   (result.1$2_0 result.0$2_0_old)
                                                                   (.1$2_0 .0$2_0_old))
                                                                  (let
                                                                     ((retval.2$2_0 retval.1$2_0)
                                                                      (b.2$2_0 b.1$2_0)
                                                                      (result.2$2_0 result.1$2_0)
                                                                      (.2$2_0 .1$2_0))
                                                                     (let
                                                                        ((retval.3$2_0 retval.2$2_0)
                                                                         (b.3$2_0 b.2$2_0)
                                                                         (result.3$2_0 result.2$2_0)
                                                                         (.3$2_0 .2$2_0))
                                                                        (let
                                                                           ((retval.4$2_0 retval.3$2_0)
                                                                            (b.4$2_0 b.3$2_0)
                                                                            (result.4$2_0 result.3$2_0)
                                                                            (.4$2_0 .3$2_0))
                                                                           (let
                                                                              ((retval.0$2_0 retval.4$2_0)
                                                                               (b.0$2_0 b.4$2_0)
                                                                               (result.0$2_0 result.4$2_0)
                                                                               (.0$2_0 .4$2_0))
                                                                              (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          (not _$2_6)
                                          (let
                                             ((_$2_7 (< .0$2_0_old 100)))
                                             (=>
                                                (not _$2_7)
                                                (let
                                                   ((_$2_9 (< .0$2_0_old 1000)))
                                                   (=>
                                                      (not _$2_9)
                                                      (let
                                                         ((_$2_11 (< .0$2_0_old 10000)))
                                                         (=>
                                                            (not _$2_11)
                                                            (let
                                                               ((_$2_13 (div
                                                                   .0$2_0_old
                                                                   10000))
                                                                (_$2_14 (+ result.0$2_0_old 4)))
                                                               (let
                                                                  ((retval.1$2_0 retval.0$2_0_old)
                                                                   (b.1$2_0 b.0$2_0_old)
                                                                   (result.1$2_0 _$2_14)
                                                                   (.1$2_0 _$2_13))
                                                                  (let
                                                                     ((retval.2$2_0 retval.1$2_0)
                                                                      (b.2$2_0 b.1$2_0)
                                                                      (result.2$2_0 result.1$2_0)
                                                                      (.2$2_0 .1$2_0))
                                                                     (let
                                                                        ((retval.3$2_0 retval.2$2_0)
                                                                         (b.3$2_0 b.2$2_0)
                                                                         (result.3$2_0 result.2$2_0)
                                                                         (.3$2_0 .2$2_0))
                                                                        (let
                                                                           ((retval.4$2_0 retval.3$2_0)
                                                                            (b.4$2_0 b.3$2_0)
                                                                            (result.4$2_0 result.3$2_0)
                                                                            (.4$2_0 .3$2_0))
                                                                           (let
                                                                              ((retval.0$2_0 retval.4$2_0)
                                                                               (b.0$2_0 b.4$2_0)
                                                                               (result.0$2_0 result.4$2_0)
                                                                               (.0$2_0 .4$2_0))
                                                                              (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))))))))))
; forbidden main
; offbyn main
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0))
                                                         (=>
                                                            (and
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              _$2_6
                                                                              (let
                                                                                 ((retval.4$2_0 result.0$2_0_old)
                                                                                  (b.4$2_0 0)
                                                                                  (result.4$2_0 result.0$2_0_old)
                                                                                  (.4$2_0 .0$2_0_old))
                                                                                 (let
                                                                                    ((retval.0$2_0 retval.4$2_0)
                                                                                     (b.0$2_0 b.4$2_0)
                                                                                     (result.0$2_0 result.4$2_0)
                                                                                     (.0$2_0 .4$2_0))
                                                                                    false)))))))
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              (not _$2_6)
                                                                              (let
                                                                                 ((_$2_7 (< .0$2_0_old 100)))
                                                                                 (=>
                                                                                    _$2_7
                                                                                    (let
                                                                                       ((_$2_8 (+ result.0$2_0_old 1)))
                                                                                       (let
                                                                                          ((retval.3$2_0 _$2_8)
                                                                                           (b.3$2_0 0)
                                                                                           (result.3$2_0 result.0$2_0_old)
                                                                                           (.3$2_0 .0$2_0_old))
                                                                                          (let
                                                                                             ((retval.4$2_0 retval.3$2_0)
                                                                                              (b.4$2_0 b.3$2_0)
                                                                                              (result.4$2_0 result.3$2_0)
                                                                                              (.4$2_0 .3$2_0))
                                                                                             (let
                                                                                                ((retval.0$2_0 retval.4$2_0)
                                                                                                 (b.0$2_0 b.4$2_0)
                                                                                                 (result.0$2_0 result.4$2_0)
                                                                                                 (.0$2_0 .4$2_0))
                                                                                                false)))))))))))
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              (not _$2_6)
                                                                              (let
                                                                                 ((_$2_7 (< .0$2_0_old 100)))
                                                                                 (=>
                                                                                    (not _$2_7)
                                                                                    (let
                                                                                       ((_$2_9 (< .0$2_0_old 1000)))
                                                                                       (=>
                                                                                          _$2_9
                                                                                          (let
                                                                                             ((_$2_10 (+ result.0$2_0_old 2)))
                                                                                             (let
                                                                                                ((retval.2$2_0 _$2_10)
                                                                                                 (b.2$2_0 0)
                                                                                                 (result.2$2_0 result.0$2_0_old)
                                                                                                 (.2$2_0 .0$2_0_old))
                                                                                                (let
                                                                                                   ((retval.3$2_0 retval.2$2_0)
                                                                                                    (b.3$2_0 b.2$2_0)
                                                                                                    (result.3$2_0 result.2$2_0)
                                                                                                    (.3$2_0 .2$2_0))
                                                                                                   (let
                                                                                                      ((retval.4$2_0 retval.3$2_0)
                                                                                                       (b.4$2_0 b.3$2_0)
                                                                                                       (result.4$2_0 result.3$2_0)
                                                                                                       (.4$2_0 .3$2_0))
                                                                                                      (let
                                                                                                         ((retval.0$2_0 retval.4$2_0)
                                                                                                          (b.0$2_0 b.4$2_0)
                                                                                                          (result.0$2_0 result.4$2_0)
                                                                                                          (.0$2_0 .4$2_0))
                                                                                                         false))))))))))))))
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              (not _$2_6)
                                                                              (let
                                                                                 ((_$2_7 (< .0$2_0_old 100)))
                                                                                 (=>
                                                                                    (not _$2_7)
                                                                                    (let
                                                                                       ((_$2_9 (< .0$2_0_old 1000)))
                                                                                       (=>
                                                                                          (not _$2_9)
                                                                                          (let
                                                                                             ((_$2_11 (< .0$2_0_old 10000)))
                                                                                             (=>
                                                                                                _$2_11
                                                                                                (let
                                                                                                   ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                                   (let
                                                                                                      ((retval.1$2_0 _$2_12)
                                                                                                       (b.1$2_0 0)
                                                                                                       (result.1$2_0 result.0$2_0_old)
                                                                                                       (.1$2_0 .0$2_0_old))
                                                                                                      (let
                                                                                                         ((retval.2$2_0 retval.1$2_0)
                                                                                                          (b.2$2_0 b.1$2_0)
                                                                                                          (result.2$2_0 result.1$2_0)
                                                                                                          (.2$2_0 .1$2_0))
                                                                                                         (let
                                                                                                            ((retval.3$2_0 retval.2$2_0)
                                                                                                             (b.3$2_0 b.2$2_0)
                                                                                                             (result.3$2_0 result.2$2_0)
                                                                                                             (.3$2_0 .2$2_0))
                                                                                                            (let
                                                                                                               ((retval.4$2_0 retval.3$2_0)
                                                                                                                (b.4$2_0 b.3$2_0)
                                                                                                                (result.4$2_0 result.3$2_0)
                                                                                                                (.4$2_0 .3$2_0))
                                                                                                               (let
                                                                                                                  ((retval.0$2_0 retval.4$2_0)
                                                                                                                   (b.0$2_0 b.4$2_0)
                                                                                                                   (result.0$2_0 result.4$2_0)
                                                                                                                   (.0$2_0 .4$2_0))
                                                                                                                  false)))))))))))))))))
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              (not _$2_6)
                                                                              (let
                                                                                 ((_$2_7 (< .0$2_0_old 100)))
                                                                                 (=>
                                                                                    (not _$2_7)
                                                                                    (let
                                                                                       ((_$2_9 (< .0$2_0_old 1000)))
                                                                                       (=>
                                                                                          (not _$2_9)
                                                                                          (let
                                                                                             ((_$2_11 (< .0$2_0_old 10000)))
                                                                                             (=>
                                                                                                (not _$2_11)
                                                                                                (let
                                                                                                   ((_$2_13 (div
                                                                                                       .0$2_0_old
                                                                                                       10000))
                                                                                                    (_$2_14 (+ result.0$2_0_old 4)))
                                                                                                   (let
                                                                                                      ((retval.1$2_0 retval.0$2_0_old)
                                                                                                       (b.1$2_0 b.0$2_0_old)
                                                                                                       (result.1$2_0 _$2_14)
                                                                                                       (.1$2_0 _$2_13))
                                                                                                      (let
                                                                                                         ((retval.2$2_0 retval.1$2_0)
                                                                                                          (b.2$2_0 b.1$2_0)
                                                                                                          (result.2$2_0 result.1$2_0)
                                                                                                          (.2$2_0 .1$2_0))
                                                                                                         (let
                                                                                                            ((retval.3$2_0 retval.2$2_0)
                                                                                                             (b.3$2_0 b.2$2_0)
                                                                                                             (result.3$2_0 result.2$2_0)
                                                                                                             (.3$2_0 .2$2_0))
                                                                                                            (let
                                                                                                               ((retval.4$2_0 retval.3$2_0)
                                                                                                                (b.4$2_0 b.3$2_0)
                                                                                                                (result.4$2_0 result.3$2_0)
                                                                                                                (.4$2_0 .3$2_0))
                                                                                                               (let
                                                                                                                  ((retval.0$2_0 retval.4$2_0)
                                                                                                                   (b.0$2_0 b.4$2_0)
                                                                                                                   (result.0$2_0 result.4$2_0)
                                                                                                                   (.0$2_0 .4$2_0))
                                                                                                                  false))))))))))))))))))
                                                            (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0))
                                                      (=>
                                                         (and
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           _$2_6
                                                                           (let
                                                                              ((retval.4$2_0 result.0$2_0_old)
                                                                               (b.4$2_0 0)
                                                                               (result.4$2_0 result.0$2_0_old)
                                                                               (.4$2_0 .0$2_0_old))
                                                                              (let
                                                                                 ((retval.0$2_0 retval.4$2_0)
                                                                                  (b.0$2_0 b.4$2_0)
                                                                                  (result.0$2_0 result.4$2_0)
                                                                                  (.0$2_0 .4$2_0))
                                                                                 false)))))))
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           (not _$2_6)
                                                                           (let
                                                                              ((_$2_7 (< .0$2_0_old 100)))
                                                                              (=>
                                                                                 _$2_7
                                                                                 (let
                                                                                    ((_$2_8 (+ result.0$2_0_old 1)))
                                                                                    (let
                                                                                       ((retval.3$2_0 _$2_8)
                                                                                        (b.3$2_0 0)
                                                                                        (result.3$2_0 result.0$2_0_old)
                                                                                        (.3$2_0 .0$2_0_old))
                                                                                       (let
                                                                                          ((retval.4$2_0 retval.3$2_0)
                                                                                           (b.4$2_0 b.3$2_0)
                                                                                           (result.4$2_0 result.3$2_0)
                                                                                           (.4$2_0 .3$2_0))
                                                                                          (let
                                                                                             ((retval.0$2_0 retval.4$2_0)
                                                                                              (b.0$2_0 b.4$2_0)
                                                                                              (result.0$2_0 result.4$2_0)
                                                                                              (.0$2_0 .4$2_0))
                                                                                             false)))))))))))
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           (not _$2_6)
                                                                           (let
                                                                              ((_$2_7 (< .0$2_0_old 100)))
                                                                              (=>
                                                                                 (not _$2_7)
                                                                                 (let
                                                                                    ((_$2_9 (< .0$2_0_old 1000)))
                                                                                    (=>
                                                                                       _$2_9
                                                                                       (let
                                                                                          ((_$2_10 (+ result.0$2_0_old 2)))
                                                                                          (let
                                                                                             ((retval.2$2_0 _$2_10)
                                                                                              (b.2$2_0 0)
                                                                                              (result.2$2_0 result.0$2_0_old)
                                                                                              (.2$2_0 .0$2_0_old))
                                                                                             (let
                                                                                                ((retval.3$2_0 retval.2$2_0)
                                                                                                 (b.3$2_0 b.2$2_0)
                                                                                                 (result.3$2_0 result.2$2_0)
                                                                                                 (.3$2_0 .2$2_0))
                                                                                                (let
                                                                                                   ((retval.4$2_0 retval.3$2_0)
                                                                                                    (b.4$2_0 b.3$2_0)
                                                                                                    (result.4$2_0 result.3$2_0)
                                                                                                    (.4$2_0 .3$2_0))
                                                                                                   (let
                                                                                                      ((retval.0$2_0 retval.4$2_0)
                                                                                                       (b.0$2_0 b.4$2_0)
                                                                                                       (result.0$2_0 result.4$2_0)
                                                                                                       (.0$2_0 .4$2_0))
                                                                                                      false))))))))))))))
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           (not _$2_6)
                                                                           (let
                                                                              ((_$2_7 (< .0$2_0_old 100)))
                                                                              (=>
                                                                                 (not _$2_7)
                                                                                 (let
                                                                                    ((_$2_9 (< .0$2_0_old 1000)))
                                                                                    (=>
                                                                                       (not _$2_9)
                                                                                       (let
                                                                                          ((_$2_11 (< .0$2_0_old 10000)))
                                                                                          (=>
                                                                                             _$2_11
                                                                                             (let
                                                                                                ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                                (let
                                                                                                   ((retval.1$2_0 _$2_12)
                                                                                                    (b.1$2_0 0)
                                                                                                    (result.1$2_0 result.0$2_0_old)
                                                                                                    (.1$2_0 .0$2_0_old))
                                                                                                   (let
                                                                                                      ((retval.2$2_0 retval.1$2_0)
                                                                                                       (b.2$2_0 b.1$2_0)
                                                                                                       (result.2$2_0 result.1$2_0)
                                                                                                       (.2$2_0 .1$2_0))
                                                                                                      (let
                                                                                                         ((retval.3$2_0 retval.2$2_0)
                                                                                                          (b.3$2_0 b.2$2_0)
                                                                                                          (result.3$2_0 result.2$2_0)
                                                                                                          (.3$2_0 .2$2_0))
                                                                                                         (let
                                                                                                            ((retval.4$2_0 retval.3$2_0)
                                                                                                             (b.4$2_0 b.3$2_0)
                                                                                                             (result.4$2_0 result.3$2_0)
                                                                                                             (.4$2_0 .3$2_0))
                                                                                                            (let
                                                                                                               ((retval.0$2_0 retval.4$2_0)
                                                                                                                (b.0$2_0 b.4$2_0)
                                                                                                                (result.0$2_0 result.4$2_0)
                                                                                                                (.0$2_0 .4$2_0))
                                                                                                               false)))))))))))))))))
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           (not _$2_6)
                                                                           (let
                                                                              ((_$2_7 (< .0$2_0_old 100)))
                                                                              (=>
                                                                                 (not _$2_7)
                                                                                 (let
                                                                                    ((_$2_9 (< .0$2_0_old 1000)))
                                                                                    (=>
                                                                                       (not _$2_9)
                                                                                       (let
                                                                                          ((_$2_11 (< .0$2_0_old 10000)))
                                                                                          (=>
                                                                                             (not _$2_11)
                                                                                             (let
                                                                                                ((_$2_13 (div
                                                                                                    .0$2_0_old
                                                                                                    10000))
                                                                                                 (_$2_14 (+ result.0$2_0_old 4)))
                                                                                                (let
                                                                                                   ((retval.1$2_0 retval.0$2_0_old)
                                                                                                    (b.1$2_0 b.0$2_0_old)
                                                                                                    (result.1$2_0 _$2_14)
                                                                                                    (.1$2_0 _$2_13))
                                                                                                   (let
                                                                                                      ((retval.2$2_0 retval.1$2_0)
                                                                                                       (b.2$2_0 b.1$2_0)
                                                                                                       (result.2$2_0 result.1$2_0)
                                                                                                       (.2$2_0 .1$2_0))
                                                                                                      (let
                                                                                                         ((retval.3$2_0 retval.2$2_0)
                                                                                                          (b.3$2_0 b.2$2_0)
                                                                                                          (result.3$2_0 result.2$2_0)
                                                                                                          (.3$2_0 .2$2_0))
                                                                                                         (let
                                                                                                            ((retval.4$2_0 retval.3$2_0)
                                                                                                             (b.4$2_0 b.3$2_0)
                                                                                                             (result.4$2_0 result.3$2_0)
                                                                                                             (.4$2_0 .3$2_0))
                                                                                                            (let
                                                                                                               ((retval.0$2_0 retval.4$2_0)
                                                                                                                (b.0$2_0 b.4$2_0)
                                                                                                                (result.0$2_0 result.4$2_0)
                                                                                                                (.0$2_0 .4$2_0))
                                                                                                               false))))))))))))))))))
                                                         (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0))
                                          (=>
                                             (and
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               _$2_6
                                                               (let
                                                                  ((retval.4$2_0 result.0$2_0_old)
                                                                   (b.4$2_0 0)
                                                                   (result.4$2_0 result.0$2_0_old)
                                                                   (.4$2_0 .0$2_0_old))
                                                                  (let
                                                                     ((retval.0$2_0 retval.4$2_0)
                                                                      (b.0$2_0 b.4$2_0)
                                                                      (result.0$2_0 result.4$2_0)
                                                                      (.0$2_0 .4$2_0))
                                                                     false)))))))
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               (not _$2_6)
                                                               (let
                                                                  ((_$2_7 (< .0$2_0_old 100)))
                                                                  (=>
                                                                     _$2_7
                                                                     (let
                                                                        ((_$2_8 (+ result.0$2_0_old 1)))
                                                                        (let
                                                                           ((retval.3$2_0 _$2_8)
                                                                            (b.3$2_0 0)
                                                                            (result.3$2_0 result.0$2_0_old)
                                                                            (.3$2_0 .0$2_0_old))
                                                                           (let
                                                                              ((retval.4$2_0 retval.3$2_0)
                                                                               (b.4$2_0 b.3$2_0)
                                                                               (result.4$2_0 result.3$2_0)
                                                                               (.4$2_0 .3$2_0))
                                                                              (let
                                                                                 ((retval.0$2_0 retval.4$2_0)
                                                                                  (b.0$2_0 b.4$2_0)
                                                                                  (result.0$2_0 result.4$2_0)
                                                                                  (.0$2_0 .4$2_0))
                                                                                 false)))))))))))
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               (not _$2_6)
                                                               (let
                                                                  ((_$2_7 (< .0$2_0_old 100)))
                                                                  (=>
                                                                     (not _$2_7)
                                                                     (let
                                                                        ((_$2_9 (< .0$2_0_old 1000)))
                                                                        (=>
                                                                           _$2_9
                                                                           (let
                                                                              ((_$2_10 (+ result.0$2_0_old 2)))
                                                                              (let
                                                                                 ((retval.2$2_0 _$2_10)
                                                                                  (b.2$2_0 0)
                                                                                  (result.2$2_0 result.0$2_0_old)
                                                                                  (.2$2_0 .0$2_0_old))
                                                                                 (let
                                                                                    ((retval.3$2_0 retval.2$2_0)
                                                                                     (b.3$2_0 b.2$2_0)
                                                                                     (result.3$2_0 result.2$2_0)
                                                                                     (.3$2_0 .2$2_0))
                                                                                    (let
                                                                                       ((retval.4$2_0 retval.3$2_0)
                                                                                        (b.4$2_0 b.3$2_0)
                                                                                        (result.4$2_0 result.3$2_0)
                                                                                        (.4$2_0 .3$2_0))
                                                                                       (let
                                                                                          ((retval.0$2_0 retval.4$2_0)
                                                                                           (b.0$2_0 b.4$2_0)
                                                                                           (result.0$2_0 result.4$2_0)
                                                                                           (.0$2_0 .4$2_0))
                                                                                          false))))))))))))))
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               (not _$2_6)
                                                               (let
                                                                  ((_$2_7 (< .0$2_0_old 100)))
                                                                  (=>
                                                                     (not _$2_7)
                                                                     (let
                                                                        ((_$2_9 (< .0$2_0_old 1000)))
                                                                        (=>
                                                                           (not _$2_9)
                                                                           (let
                                                                              ((_$2_11 (< .0$2_0_old 10000)))
                                                                              (=>
                                                                                 _$2_11
                                                                                 (let
                                                                                    ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                    (let
                                                                                       ((retval.1$2_0 _$2_12)
                                                                                        (b.1$2_0 0)
                                                                                        (result.1$2_0 result.0$2_0_old)
                                                                                        (.1$2_0 .0$2_0_old))
                                                                                       (let
                                                                                          ((retval.2$2_0 retval.1$2_0)
                                                                                           (b.2$2_0 b.1$2_0)
                                                                                           (result.2$2_0 result.1$2_0)
                                                                                           (.2$2_0 .1$2_0))
                                                                                          (let
                                                                                             ((retval.3$2_0 retval.2$2_0)
                                                                                              (b.3$2_0 b.2$2_0)
                                                                                              (result.3$2_0 result.2$2_0)
                                                                                              (.3$2_0 .2$2_0))
                                                                                             (let
                                                                                                ((retval.4$2_0 retval.3$2_0)
                                                                                                 (b.4$2_0 b.3$2_0)
                                                                                                 (result.4$2_0 result.3$2_0)
                                                                                                 (.4$2_0 .3$2_0))
                                                                                                (let
                                                                                                   ((retval.0$2_0 retval.4$2_0)
                                                                                                    (b.0$2_0 b.4$2_0)
                                                                                                    (result.0$2_0 result.4$2_0)
                                                                                                    (.0$2_0 .4$2_0))
                                                                                                   false)))))))))))))))))
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               (not _$2_6)
                                                               (let
                                                                  ((_$2_7 (< .0$2_0_old 100)))
                                                                  (=>
                                                                     (not _$2_7)
                                                                     (let
                                                                        ((_$2_9 (< .0$2_0_old 1000)))
                                                                        (=>
                                                                           (not _$2_9)
                                                                           (let
                                                                              ((_$2_11 (< .0$2_0_old 10000)))
                                                                              (=>
                                                                                 (not _$2_11)
                                                                                 (let
                                                                                    ((_$2_13 (div
                                                                                        .0$2_0_old
                                                                                        10000))
                                                                                     (_$2_14 (+ result.0$2_0_old 4)))
                                                                                    (let
                                                                                       ((retval.1$2_0 retval.0$2_0_old)
                                                                                        (b.1$2_0 b.0$2_0_old)
                                                                                        (result.1$2_0 _$2_14)
                                                                                        (.1$2_0 _$2_13))
                                                                                       (let
                                                                                          ((retval.2$2_0 retval.1$2_0)
                                                                                           (b.2$2_0 b.1$2_0)
                                                                                           (result.2$2_0 result.1$2_0)
                                                                                           (.2$2_0 .1$2_0))
                                                                                          (let
                                                                                             ((retval.3$2_0 retval.2$2_0)
                                                                                              (b.3$2_0 b.2$2_0)
                                                                                              (result.3$2_0 result.2$2_0)
                                                                                              (.3$2_0 .2$2_0))
                                                                                             (let
                                                                                                ((retval.4$2_0 retval.3$2_0)
                                                                                                 (b.4$2_0 b.3$2_0)
                                                                                                 (result.4$2_0 result.3$2_0)
                                                                                                 (.4$2_0 .3$2_0))
                                                                                                (let
                                                                                                   ((retval.0$2_0 retval.4$2_0)
                                                                                                    (b.0$2_0 b.4$2_0)
                                                                                                    (result.0$2_0 result.4$2_0)
                                                                                                    (.0$2_0 .4$2_0))
                                                                                                   false))))))))))))))))))
                                             (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0))
                              (=>
                                 (and
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   _$2_6
                                                   (let
                                                      ((retval.4$2_0 result.0$2_0_old)
                                                       (b.4$2_0 0)
                                                       (result.4$2_0 result.0$2_0_old)
                                                       (.4$2_0 .0$2_0_old))
                                                      (let
                                                         ((retval.0$2_0 retval.4$2_0)
                                                          (b.0$2_0 b.4$2_0)
                                                          (result.0$2_0 result.4$2_0)
                                                          (.0$2_0 .4$2_0))
                                                         false)))))))
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   (not _$2_6)
                                                   (let
                                                      ((_$2_7 (< .0$2_0_old 100)))
                                                      (=>
                                                         _$2_7
                                                         (let
                                                            ((_$2_8 (+ result.0$2_0_old 1)))
                                                            (let
                                                               ((retval.3$2_0 _$2_8)
                                                                (b.3$2_0 0)
                                                                (result.3$2_0 result.0$2_0_old)
                                                                (.3$2_0 .0$2_0_old))
                                                               (let
                                                                  ((retval.4$2_0 retval.3$2_0)
                                                                   (b.4$2_0 b.3$2_0)
                                                                   (result.4$2_0 result.3$2_0)
                                                                   (.4$2_0 .3$2_0))
                                                                  (let
                                                                     ((retval.0$2_0 retval.4$2_0)
                                                                      (b.0$2_0 b.4$2_0)
                                                                      (result.0$2_0 result.4$2_0)
                                                                      (.0$2_0 .4$2_0))
                                                                     false)))))))))))
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   (not _$2_6)
                                                   (let
                                                      ((_$2_7 (< .0$2_0_old 100)))
                                                      (=>
                                                         (not _$2_7)
                                                         (let
                                                            ((_$2_9 (< .0$2_0_old 1000)))
                                                            (=>
                                                               _$2_9
                                                               (let
                                                                  ((_$2_10 (+ result.0$2_0_old 2)))
                                                                  (let
                                                                     ((retval.2$2_0 _$2_10)
                                                                      (b.2$2_0 0)
                                                                      (result.2$2_0 result.0$2_0_old)
                                                                      (.2$2_0 .0$2_0_old))
                                                                     (let
                                                                        ((retval.3$2_0 retval.2$2_0)
                                                                         (b.3$2_0 b.2$2_0)
                                                                         (result.3$2_0 result.2$2_0)
                                                                         (.3$2_0 .2$2_0))
                                                                        (let
                                                                           ((retval.4$2_0 retval.3$2_0)
                                                                            (b.4$2_0 b.3$2_0)
                                                                            (result.4$2_0 result.3$2_0)
                                                                            (.4$2_0 .3$2_0))
                                                                           (let
                                                                              ((retval.0$2_0 retval.4$2_0)
                                                                               (b.0$2_0 b.4$2_0)
                                                                               (result.0$2_0 result.4$2_0)
                                                                               (.0$2_0 .4$2_0))
                                                                              false))))))))))))))
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   (not _$2_6)
                                                   (let
                                                      ((_$2_7 (< .0$2_0_old 100)))
                                                      (=>
                                                         (not _$2_7)
                                                         (let
                                                            ((_$2_9 (< .0$2_0_old 1000)))
                                                            (=>
                                                               (not _$2_9)
                                                               (let
                                                                  ((_$2_11 (< .0$2_0_old 10000)))
                                                                  (=>
                                                                     _$2_11
                                                                     (let
                                                                        ((_$2_12 (+ result.0$2_0_old 3)))
                                                                        (let
                                                                           ((retval.1$2_0 _$2_12)
                                                                            (b.1$2_0 0)
                                                                            (result.1$2_0 result.0$2_0_old)
                                                                            (.1$2_0 .0$2_0_old))
                                                                           (let
                                                                              ((retval.2$2_0 retval.1$2_0)
                                                                               (b.2$2_0 b.1$2_0)
                                                                               (result.2$2_0 result.1$2_0)
                                                                               (.2$2_0 .1$2_0))
                                                                              (let
                                                                                 ((retval.3$2_0 retval.2$2_0)
                                                                                  (b.3$2_0 b.2$2_0)
                                                                                  (result.3$2_0 result.2$2_0)
                                                                                  (.3$2_0 .2$2_0))
                                                                                 (let
                                                                                    ((retval.4$2_0 retval.3$2_0)
                                                                                     (b.4$2_0 b.3$2_0)
                                                                                     (result.4$2_0 result.3$2_0)
                                                                                     (.4$2_0 .3$2_0))
                                                                                    (let
                                                                                       ((retval.0$2_0 retval.4$2_0)
                                                                                        (b.0$2_0 b.4$2_0)
                                                                                        (result.0$2_0 result.4$2_0)
                                                                                        (.0$2_0 .4$2_0))
                                                                                       false)))))))))))))))))
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   (not _$2_6)
                                                   (let
                                                      ((_$2_7 (< .0$2_0_old 100)))
                                                      (=>
                                                         (not _$2_7)
                                                         (let
                                                            ((_$2_9 (< .0$2_0_old 1000)))
                                                            (=>
                                                               (not _$2_9)
                                                               (let
                                                                  ((_$2_11 (< .0$2_0_old 10000)))
                                                                  (=>
                                                                     (not _$2_11)
                                                                     (let
                                                                        ((_$2_13 (div
                                                                            .0$2_0_old
                                                                            10000))
                                                                         (_$2_14 (+ result.0$2_0_old 4)))
                                                                        (let
                                                                           ((retval.1$2_0 retval.0$2_0_old)
                                                                            (b.1$2_0 b.0$2_0_old)
                                                                            (result.1$2_0 _$2_14)
                                                                            (.1$2_0 _$2_13))
                                                                           (let
                                                                              ((retval.2$2_0 retval.1$2_0)
                                                                               (b.2$2_0 b.1$2_0)
                                                                               (result.2$2_0 result.1$2_0)
                                                                               (.2$2_0 .1$2_0))
                                                                              (let
                                                                                 ((retval.3$2_0 retval.2$2_0)
                                                                                  (b.3$2_0 b.2$2_0)
                                                                                  (result.3$2_0 result.2$2_0)
                                                                                  (.3$2_0 .2$2_0))
                                                                                 (let
                                                                                    ((retval.4$2_0 retval.3$2_0)
                                                                                     (b.4$2_0 b.3$2_0)
                                                                                     (result.4$2_0 result.3$2_0)
                                                                                     (.4$2_0 .3$2_0))
                                                                                    (let
                                                                                       ((retval.0$2_0 retval.4$2_0)
                                                                                        (b.0$2_0 b.4$2_0)
                                                                                        (result.0$2_0 result.4$2_0)
                                                                                        (.0$2_0 .4$2_0))
                                                                                       false))))))))))))))))))
                                 (INV_42_MAIN .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        _$2_6
                        (let
                           ((retval.4$2_0 result.0$2_0_old)
                            (b.4$2_0 0)
                            (result.4$2_0 result.0$2_0_old)
                            (.4$2_0 .0$2_0_old))
                           (let
                              ((retval.0$2_0 retval.4$2_0)
                               (b.0$2_0 b.4$2_0)
                               (result.0$2_0 result.4$2_0)
                               (.0$2_0 .4$2_0))
                              (=>
                                 (and
                                    (let
                                       ((_$1_2 (> .0$1_0_old 0)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ result.0$1_0_old 1))
                                              (_$1_7 (div
                                                 .0$1_0_old
                                                 10)))
                                             (let
                                                ((_$1_8 (> _$1_7 0)))
                                                (=>
                                                   _$1_8
                                                   (let
                                                      ((_$1_9 (+ _$1_6 1))
                                                       (_$1_10 (div
                                                          _$1_7
                                                          10)))
                                                      (let
                                                         ((_$1_11 (> _$1_10 0)))
                                                         (=>
                                                            _$1_11
                                                            (let
                                                               ((_$1_12 (+ _$1_9 1))
                                                                (_$1_13 (div
                                                                   _$1_10
                                                                   10)))
                                                               (let
                                                                  ((_$1_14 (> _$1_13 0)))
                                                                  (=>
                                                                     _$1_14
                                                                     (let
                                                                        ((_$1_15 (+ _$1_12 1))
                                                                         (_$1_16 (div
                                                                            _$1_13
                                                                            10)))
                                                                        (let
                                                                           ((result.1$1_0 _$1_15)
                                                                            (.1$1_0 _$1_16))
                                                                           (let
                                                                              ((result.2$1_0 result.1$1_0)
                                                                               (.2$1_0 .1$1_0))
                                                                              (let
                                                                                 ((result.3$1_0 result.2$1_0)
                                                                                  (.3$1_0 .2$1_0))
                                                                                 (let
                                                                                    ((result.0$1_0 result.3$1_0)
                                                                                     (.0$1_0 .3$1_0))
                                                                                    false))))))))))))))))
                                    (let
                                       ((_$1_2 (> .0$1_0_old 0)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ result.0$1_0_old 1))
                                              (_$1_7 (div
                                                 .0$1_0_old
                                                 10)))
                                             (let
                                                ((_$1_8 (> _$1_7 0)))
                                                (=>
                                                   _$1_8
                                                   (let
                                                      ((_$1_9 (+ _$1_6 1))
                                                       (_$1_10 (div
                                                          _$1_7
                                                          10)))
                                                      (let
                                                         ((_$1_11 (> _$1_10 0)))
                                                         (=>
                                                            _$1_11
                                                            (let
                                                               ((_$1_12 (+ _$1_9 1))
                                                                (_$1_13 (div
                                                                   _$1_10
                                                                   10)))
                                                               (let
                                                                  ((_$1_14 (> _$1_13 0)))
                                                                  (=>
                                                                     (not _$1_14)
                                                                     (let
                                                                        ((result.1$1_0 _$1_12)
                                                                         (.1$1_0 _$1_13))
                                                                        (let
                                                                           ((result.2$1_0 result.1$1_0)
                                                                            (.2$1_0 .1$1_0))
                                                                           (let
                                                                              ((result.3$1_0 result.2$1_0)
                                                                               (.3$1_0 .2$1_0))
                                                                              (let
                                                                                 ((result.0$1_0 result.3$1_0)
                                                                                  (.0$1_0 .3$1_0))
                                                                                 false)))))))))))))))
                                    (let
                                       ((_$1_2 (> .0$1_0_old 0)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ result.0$1_0_old 1))
                                              (_$1_7 (div
                                                 .0$1_0_old
                                                 10)))
                                             (let
                                                ((_$1_8 (> _$1_7 0)))
                                                (=>
                                                   _$1_8
                                                   (let
                                                      ((_$1_9 (+ _$1_6 1))
                                                       (_$1_10 (div
                                                          _$1_7
                                                          10)))
                                                      (let
                                                         ((_$1_11 (> _$1_10 0)))
                                                         (=>
                                                            (not _$1_11)
                                                            (let
                                                               ((result.2$1_0 _$1_9)
                                                                (.2$1_0 _$1_10))
                                                               (let
                                                                  ((result.3$1_0 result.2$1_0)
                                                                   (.3$1_0 .2$1_0))
                                                                  (let
                                                                     ((result.0$1_0 result.3$1_0)
                                                                      (.0$1_0 .3$1_0))
                                                                     false)))))))))))
                                    (let
                                       ((_$1_2 (> .0$1_0_old 0)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ result.0$1_0_old 1))
                                              (_$1_7 (div
                                                 .0$1_0_old
                                                 10)))
                                             (let
                                                ((_$1_8 (> _$1_7 0)))
                                                (=>
                                                   (not _$1_8)
                                                   (let
                                                      ((result.3$1_0 _$1_6)
                                                       (.3$1_0 _$1_7))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0))
                                                         false))))))))
                                 (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              _$2_7
                              (let
                                 ((_$2_8 (+ result.0$2_0_old 1)))
                                 (let
                                    ((retval.3$2_0 _$2_8)
                                     (b.3$2_0 0)
                                     (result.3$2_0 result.0$2_0_old)
                                     (.3$2_0 .0$2_0_old))
                                    (let
                                       ((retval.4$2_0 retval.3$2_0)
                                        (b.4$2_0 b.3$2_0)
                                        (result.4$2_0 result.3$2_0)
                                        (.4$2_0 .3$2_0))
                                       (let
                                          ((retval.0$2_0 retval.4$2_0)
                                           (b.0$2_0 b.4$2_0)
                                           (result.0$2_0 result.4$2_0)
                                           (.0$2_0 .4$2_0))
                                          (=>
                                             (and
                                                (let
                                                   ((_$1_2 (> .0$1_0_old 0)))
                                                   (=>
                                                      _$1_2
                                                      (let
                                                         ((_$1_6 (+ result.0$1_0_old 1))
                                                          (_$1_7 (div
                                                             .0$1_0_old
                                                             10)))
                                                         (let
                                                            ((_$1_8 (> _$1_7 0)))
                                                            (=>
                                                               _$1_8
                                                               (let
                                                                  ((_$1_9 (+ _$1_6 1))
                                                                   (_$1_10 (div
                                                                      _$1_7
                                                                      10)))
                                                                  (let
                                                                     ((_$1_11 (> _$1_10 0)))
                                                                     (=>
                                                                        _$1_11
                                                                        (let
                                                                           ((_$1_12 (+ _$1_9 1))
                                                                            (_$1_13 (div
                                                                               _$1_10
                                                                               10)))
                                                                           (let
                                                                              ((_$1_14 (> _$1_13 0)))
                                                                              (=>
                                                                                 _$1_14
                                                                                 (let
                                                                                    ((_$1_15 (+ _$1_12 1))
                                                                                     (_$1_16 (div
                                                                                        _$1_13
                                                                                        10)))
                                                                                    (let
                                                                                       ((result.1$1_0 _$1_15)
                                                                                        (.1$1_0 _$1_16))
                                                                                       (let
                                                                                          ((result.2$1_0 result.1$1_0)
                                                                                           (.2$1_0 .1$1_0))
                                                                                          (let
                                                                                             ((result.3$1_0 result.2$1_0)
                                                                                              (.3$1_0 .2$1_0))
                                                                                             (let
                                                                                                ((result.0$1_0 result.3$1_0)
                                                                                                 (.0$1_0 .3$1_0))
                                                                                                false))))))))))))))))
                                                (let
                                                   ((_$1_2 (> .0$1_0_old 0)))
                                                   (=>
                                                      _$1_2
                                                      (let
                                                         ((_$1_6 (+ result.0$1_0_old 1))
                                                          (_$1_7 (div
                                                             .0$1_0_old
                                                             10)))
                                                         (let
                                                            ((_$1_8 (> _$1_7 0)))
                                                            (=>
                                                               _$1_8
                                                               (let
                                                                  ((_$1_9 (+ _$1_6 1))
                                                                   (_$1_10 (div
                                                                      _$1_7
                                                                      10)))
                                                                  (let
                                                                     ((_$1_11 (> _$1_10 0)))
                                                                     (=>
                                                                        _$1_11
                                                                        (let
                                                                           ((_$1_12 (+ _$1_9 1))
                                                                            (_$1_13 (div
                                                                               _$1_10
                                                                               10)))
                                                                           (let
                                                                              ((_$1_14 (> _$1_13 0)))
                                                                              (=>
                                                                                 (not _$1_14)
                                                                                 (let
                                                                                    ((result.1$1_0 _$1_12)
                                                                                     (.1$1_0 _$1_13))
                                                                                    (let
                                                                                       ((result.2$1_0 result.1$1_0)
                                                                                        (.2$1_0 .1$1_0))
                                                                                       (let
                                                                                          ((result.3$1_0 result.2$1_0)
                                                                                           (.3$1_0 .2$1_0))
                                                                                          (let
                                                                                             ((result.0$1_0 result.3$1_0)
                                                                                              (.0$1_0 .3$1_0))
                                                                                             false)))))))))))))))
                                                (let
                                                   ((_$1_2 (> .0$1_0_old 0)))
                                                   (=>
                                                      _$1_2
                                                      (let
                                                         ((_$1_6 (+ result.0$1_0_old 1))
                                                          (_$1_7 (div
                                                             .0$1_0_old
                                                             10)))
                                                         (let
                                                            ((_$1_8 (> _$1_7 0)))
                                                            (=>
                                                               _$1_8
                                                               (let
                                                                  ((_$1_9 (+ _$1_6 1))
                                                                   (_$1_10 (div
                                                                      _$1_7
                                                                      10)))
                                                                  (let
                                                                     ((_$1_11 (> _$1_10 0)))
                                                                     (=>
                                                                        (not _$1_11)
                                                                        (let
                                                                           ((result.2$1_0 _$1_9)
                                                                            (.2$1_0 _$1_10))
                                                                           (let
                                                                              ((result.3$1_0 result.2$1_0)
                                                                               (.3$1_0 .2$1_0))
                                                                              (let
                                                                                 ((result.0$1_0 result.3$1_0)
                                                                                  (.0$1_0 .3$1_0))
                                                                                 false)))))))))))
                                                (let
                                                   ((_$1_2 (> .0$1_0_old 0)))
                                                   (=>
                                                      _$1_2
                                                      (let
                                                         ((_$1_6 (+ result.0$1_0_old 1))
                                                          (_$1_7 (div
                                                             .0$1_0_old
                                                             10)))
                                                         (let
                                                            ((_$1_8 (> _$1_7 0)))
                                                            (=>
                                                               (not _$1_8)
                                                               (let
                                                                  ((result.3$1_0 _$1_6)
                                                                   (.3$1_0 _$1_7))
                                                                  (let
                                                                     ((result.0$1_0 result.3$1_0)
                                                                      (.0$1_0 .3$1_0))
                                                                     false))))))))
                                             (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((_$2_9 (< .0$2_0_old 1000)))
                                 (=>
                                    _$2_9
                                    (let
                                       ((_$2_10 (+ result.0$2_0_old 2)))
                                       (let
                                          ((retval.2$2_0 _$2_10)
                                           (b.2$2_0 0)
                                           (result.2$2_0 result.0$2_0_old)
                                           (.2$2_0 .0$2_0_old))
                                          (let
                                             ((retval.3$2_0 retval.2$2_0)
                                              (b.3$2_0 b.2$2_0)
                                              (result.3$2_0 result.2$2_0)
                                              (.3$2_0 .2$2_0))
                                             (let
                                                ((retval.4$2_0 retval.3$2_0)
                                                 (b.4$2_0 b.3$2_0)
                                                 (result.4$2_0 result.3$2_0)
                                                 (.4$2_0 .3$2_0))
                                                (let
                                                   ((retval.0$2_0 retval.4$2_0)
                                                    (b.0$2_0 b.4$2_0)
                                                    (result.0$2_0 result.4$2_0)
                                                    (.0$2_0 .4$2_0))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((_$1_2 (> .0$1_0_old 0)))
                                                            (=>
                                                               _$1_2
                                                               (let
                                                                  ((_$1_6 (+ result.0$1_0_old 1))
                                                                   (_$1_7 (div
                                                                      .0$1_0_old
                                                                      10)))
                                                                  (let
                                                                     ((_$1_8 (> _$1_7 0)))
                                                                     (=>
                                                                        _$1_8
                                                                        (let
                                                                           ((_$1_9 (+ _$1_6 1))
                                                                            (_$1_10 (div
                                                                               _$1_7
                                                                               10)))
                                                                           (let
                                                                              ((_$1_11 (> _$1_10 0)))
                                                                              (=>
                                                                                 _$1_11
                                                                                 (let
                                                                                    ((_$1_12 (+ _$1_9 1))
                                                                                     (_$1_13 (div
                                                                                        _$1_10
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_14 (> _$1_13 0)))
                                                                                       (=>
                                                                                          _$1_14
                                                                                          (let
                                                                                             ((_$1_15 (+ _$1_12 1))
                                                                                              (_$1_16 (div
                                                                                                 _$1_13
                                                                                                 10)))
                                                                                             (let
                                                                                                ((result.1$1_0 _$1_15)
                                                                                                 (.1$1_0 _$1_16))
                                                                                                (let
                                                                                                   ((result.2$1_0 result.1$1_0)
                                                                                                    (.2$1_0 .1$1_0))
                                                                                                   (let
                                                                                                      ((result.3$1_0 result.2$1_0)
                                                                                                       (.3$1_0 .2$1_0))
                                                                                                      (let
                                                                                                         ((result.0$1_0 result.3$1_0)
                                                                                                          (.0$1_0 .3$1_0))
                                                                                                         false))))))))))))))))
                                                         (let
                                                            ((_$1_2 (> .0$1_0_old 0)))
                                                            (=>
                                                               _$1_2
                                                               (let
                                                                  ((_$1_6 (+ result.0$1_0_old 1))
                                                                   (_$1_7 (div
                                                                      .0$1_0_old
                                                                      10)))
                                                                  (let
                                                                     ((_$1_8 (> _$1_7 0)))
                                                                     (=>
                                                                        _$1_8
                                                                        (let
                                                                           ((_$1_9 (+ _$1_6 1))
                                                                            (_$1_10 (div
                                                                               _$1_7
                                                                               10)))
                                                                           (let
                                                                              ((_$1_11 (> _$1_10 0)))
                                                                              (=>
                                                                                 _$1_11
                                                                                 (let
                                                                                    ((_$1_12 (+ _$1_9 1))
                                                                                     (_$1_13 (div
                                                                                        _$1_10
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_14 (> _$1_13 0)))
                                                                                       (=>
                                                                                          (not _$1_14)
                                                                                          (let
                                                                                             ((result.1$1_0 _$1_12)
                                                                                              (.1$1_0 _$1_13))
                                                                                             (let
                                                                                                ((result.2$1_0 result.1$1_0)
                                                                                                 (.2$1_0 .1$1_0))
                                                                                                (let
                                                                                                   ((result.3$1_0 result.2$1_0)
                                                                                                    (.3$1_0 .2$1_0))
                                                                                                   (let
                                                                                                      ((result.0$1_0 result.3$1_0)
                                                                                                       (.0$1_0 .3$1_0))
                                                                                                      false)))))))))))))))
                                                         (let
                                                            ((_$1_2 (> .0$1_0_old 0)))
                                                            (=>
                                                               _$1_2
                                                               (let
                                                                  ((_$1_6 (+ result.0$1_0_old 1))
                                                                   (_$1_7 (div
                                                                      .0$1_0_old
                                                                      10)))
                                                                  (let
                                                                     ((_$1_8 (> _$1_7 0)))
                                                                     (=>
                                                                        _$1_8
                                                                        (let
                                                                           ((_$1_9 (+ _$1_6 1))
                                                                            (_$1_10 (div
                                                                               _$1_7
                                                                               10)))
                                                                           (let
                                                                              ((_$1_11 (> _$1_10 0)))
                                                                              (=>
                                                                                 (not _$1_11)
                                                                                 (let
                                                                                    ((result.2$1_0 _$1_9)
                                                                                     (.2$1_0 _$1_10))
                                                                                    (let
                                                                                       ((result.3$1_0 result.2$1_0)
                                                                                        (.3$1_0 .2$1_0))
                                                                                       (let
                                                                                          ((result.0$1_0 result.3$1_0)
                                                                                           (.0$1_0 .3$1_0))
                                                                                          false)))))))))))
                                                         (let
                                                            ((_$1_2 (> .0$1_0_old 0)))
                                                            (=>
                                                               _$1_2
                                                               (let
                                                                  ((_$1_6 (+ result.0$1_0_old 1))
                                                                   (_$1_7 (div
                                                                      .0$1_0_old
                                                                      10)))
                                                                  (let
                                                                     ((_$1_8 (> _$1_7 0)))
                                                                     (=>
                                                                        (not _$1_8)
                                                                        (let
                                                                           ((result.3$1_0 _$1_6)
                                                                            (.3$1_0 _$1_7))
                                                                           (let
                                                                              ((result.0$1_0 result.3$1_0)
                                                                               (.0$1_0 .3$1_0))
                                                                              false))))))))
                                                      (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((_$2_9 (< .0$2_0_old 1000)))
                                 (=>
                                    (not _$2_9)
                                    (let
                                       ((_$2_11 (< .0$2_0_old 10000)))
                                       (=>
                                          _$2_11
                                          (let
                                             ((_$2_12 (+ result.0$2_0_old 3)))
                                             (let
                                                ((retval.1$2_0 _$2_12)
                                                 (b.1$2_0 0)
                                                 (result.1$2_0 result.0$2_0_old)
                                                 (.1$2_0 .0$2_0_old))
                                                (let
                                                   ((retval.2$2_0 retval.1$2_0)
                                                    (b.2$2_0 b.1$2_0)
                                                    (result.2$2_0 result.1$2_0)
                                                    (.2$2_0 .1$2_0))
                                                   (let
                                                      ((retval.3$2_0 retval.2$2_0)
                                                       (b.3$2_0 b.2$2_0)
                                                       (result.3$2_0 result.2$2_0)
                                                       (.3$2_0 .2$2_0))
                                                      (let
                                                         ((retval.4$2_0 retval.3$2_0)
                                                          (b.4$2_0 b.3$2_0)
                                                          (result.4$2_0 result.3$2_0)
                                                          (.4$2_0 .3$2_0))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (=>
                                                               (and
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          _$1_11
                                                                                          (let
                                                                                             ((_$1_12 (+ _$1_9 1))
                                                                                              (_$1_13 (div
                                                                                                 _$1_10
                                                                                                 10)))
                                                                                             (let
                                                                                                ((_$1_14 (> _$1_13 0)))
                                                                                                (=>
                                                                                                   _$1_14
                                                                                                   (let
                                                                                                      ((_$1_15 (+ _$1_12 1))
                                                                                                       (_$1_16 (div
                                                                                                          _$1_13
                                                                                                          10)))
                                                                                                      (let
                                                                                                         ((result.1$1_0 _$1_15)
                                                                                                          (.1$1_0 _$1_16))
                                                                                                         (let
                                                                                                            ((result.2$1_0 result.1$1_0)
                                                                                                             (.2$1_0 .1$1_0))
                                                                                                            (let
                                                                                                               ((result.3$1_0 result.2$1_0)
                                                                                                                (.3$1_0 .2$1_0))
                                                                                                               (let
                                                                                                                  ((result.0$1_0 result.3$1_0)
                                                                                                                   (.0$1_0 .3$1_0))
                                                                                                                  false))))))))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          _$1_11
                                                                                          (let
                                                                                             ((_$1_12 (+ _$1_9 1))
                                                                                              (_$1_13 (div
                                                                                                 _$1_10
                                                                                                 10)))
                                                                                             (let
                                                                                                ((_$1_14 (> _$1_13 0)))
                                                                                                (=>
                                                                                                   (not _$1_14)
                                                                                                   (let
                                                                                                      ((result.1$1_0 _$1_12)
                                                                                                       (.1$1_0 _$1_13))
                                                                                                      (let
                                                                                                         ((result.2$1_0 result.1$1_0)
                                                                                                          (.2$1_0 .1$1_0))
                                                                                                         (let
                                                                                                            ((result.3$1_0 result.2$1_0)
                                                                                                             (.3$1_0 .2$1_0))
                                                                                                            (let
                                                                                                               ((result.0$1_0 result.3$1_0)
                                                                                                                (.0$1_0 .3$1_0))
                                                                                                               false)))))))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          (not _$1_11)
                                                                                          (let
                                                                                             ((result.2$1_0 _$1_9)
                                                                                              (.2$1_0 _$1_10))
                                                                                             (let
                                                                                                ((result.3$1_0 result.2$1_0)
                                                                                                 (.3$1_0 .2$1_0))
                                                                                                (let
                                                                                                   ((result.0$1_0 result.3$1_0)
                                                                                                    (.0$1_0 .3$1_0))
                                                                                                   false)))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 (not _$1_8)
                                                                                 (let
                                                                                    ((result.3$1_0 _$1_6)
                                                                                     (.3$1_0 _$1_7))
                                                                                    (let
                                                                                       ((result.0$1_0 result.3$1_0)
                                                                                        (.0$1_0 .3$1_0))
                                                                                       false))))))))
                                                               (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((_$2_9 (< .0$2_0_old 1000)))
                                 (=>
                                    (not _$2_9)
                                    (let
                                       ((_$2_11 (< .0$2_0_old 10000)))
                                       (=>
                                          (not _$2_11)
                                          (let
                                             ((_$2_13 (div
                                                 .0$2_0_old
                                                 10000))
                                              (_$2_14 (+ result.0$2_0_old 4)))
                                             (let
                                                ((retval.1$2_0 retval.0$2_0_old)
                                                 (b.1$2_0 b.0$2_0_old)
                                                 (result.1$2_0 _$2_14)
                                                 (.1$2_0 _$2_13))
                                                (let
                                                   ((retval.2$2_0 retval.1$2_0)
                                                    (b.2$2_0 b.1$2_0)
                                                    (result.2$2_0 result.1$2_0)
                                                    (.2$2_0 .1$2_0))
                                                   (let
                                                      ((retval.3$2_0 retval.2$2_0)
                                                       (b.3$2_0 b.2$2_0)
                                                       (result.3$2_0 result.2$2_0)
                                                       (.3$2_0 .2$2_0))
                                                      (let
                                                         ((retval.4$2_0 retval.3$2_0)
                                                          (b.4$2_0 b.3$2_0)
                                                          (result.4$2_0 result.3$2_0)
                                                          (.4$2_0 .3$2_0))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (=>
                                                               (and
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          _$1_11
                                                                                          (let
                                                                                             ((_$1_12 (+ _$1_9 1))
                                                                                              (_$1_13 (div
                                                                                                 _$1_10
                                                                                                 10)))
                                                                                             (let
                                                                                                ((_$1_14 (> _$1_13 0)))
                                                                                                (=>
                                                                                                   _$1_14
                                                                                                   (let
                                                                                                      ((_$1_15 (+ _$1_12 1))
                                                                                                       (_$1_16 (div
                                                                                                          _$1_13
                                                                                                          10)))
                                                                                                      (let
                                                                                                         ((result.1$1_0 _$1_15)
                                                                                                          (.1$1_0 _$1_16))
                                                                                                         (let
                                                                                                            ((result.2$1_0 result.1$1_0)
                                                                                                             (.2$1_0 .1$1_0))
                                                                                                            (let
                                                                                                               ((result.3$1_0 result.2$1_0)
                                                                                                                (.3$1_0 .2$1_0))
                                                                                                               (let
                                                                                                                  ((result.0$1_0 result.3$1_0)
                                                                                                                   (.0$1_0 .3$1_0))
                                                                                                                  false))))))))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          _$1_11
                                                                                          (let
                                                                                             ((_$1_12 (+ _$1_9 1))
                                                                                              (_$1_13 (div
                                                                                                 _$1_10
                                                                                                 10)))
                                                                                             (let
                                                                                                ((_$1_14 (> _$1_13 0)))
                                                                                                (=>
                                                                                                   (not _$1_14)
                                                                                                   (let
                                                                                                      ((result.1$1_0 _$1_12)
                                                                                                       (.1$1_0 _$1_13))
                                                                                                      (let
                                                                                                         ((result.2$1_0 result.1$1_0)
                                                                                                          (.2$1_0 .1$1_0))
                                                                                                         (let
                                                                                                            ((result.3$1_0 result.2$1_0)
                                                                                                             (.3$1_0 .2$1_0))
                                                                                                            (let
                                                                                                               ((result.0$1_0 result.3$1_0)
                                                                                                                (.0$1_0 .3$1_0))
                                                                                                               false)))))))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          (not _$1_11)
                                                                                          (let
                                                                                             ((result.2$1_0 _$1_9)
                                                                                              (.2$1_0 _$1_10))
                                                                                             (let
                                                                                                ((result.3$1_0 result.2$1_0)
                                                                                                 (.3$1_0 .2$1_0))
                                                                                                (let
                                                                                                   ((result.0$1_0 result.3$1_0)
                                                                                                    (.0$1_0 .3$1_0))
                                                                                                   false)))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 (not _$1_8)
                                                                                 (let
                                                                                    ((result.3$1_0 _$1_6)
                                                                                     (.3$1_0 _$1_7))
                                                                                    (let
                                                                                       ((result.0$1_0 result.3$1_0)
                                                                                        (.0$1_0 .3$1_0))
                                                                                       false))))))))
                                                               (INV_42_MAIN .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0))))))))))))))))))))))
; end
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old)
         (let
            ((_$1_0 (div
                n$1_0_old
                10)))
            (let
               ((result.0$1_0 1)
                (.0$1_0 _$1_0)
                (retval.0$2_0 (- 1))
                (b.0$2_0 1)
                (result.0$2_0 1)
                (.0$2_0 n$2_0_old))
               (forall
                  ((result$1 Int)
                   (result$2 Int))
                  (and
                     (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                     (=>
                        (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                        (INV_REC_f n$1_0_old n$2_0_old result$1 result$2)))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               (not _$1_2)
               (let
                  ((result$1 result.0$1_0_old)
                   (_$2_1 (= b.0$2_0_old 0)))
                  (let
                     ((_$2_2 (xor
                         _$2_1
                         true)))
                     (=>
                        (not _$2_2)
                        (let
                           ((result$2 retval.0$2_0_old))
                           (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     _$2_6
                                                                     (let
                                                                        ((retval.4$2_0 result.0$2_0_old)
                                                                         (b.4$2_0 0)
                                                                         (result.4$2_0 result.0$2_0_old)
                                                                         (.4$2_0 .0$2_0_old))
                                                                        (let
                                                                           ((retval.0$2_0 retval.4$2_0)
                                                                            (b.0$2_0 b.4$2_0)
                                                                            (result.0$2_0 result.4$2_0)
                                                                            (.0$2_0 .4$2_0))
                                                                           (forall
                                                                              ((result$1 Int)
                                                                               (result$2 Int))
                                                                              (and
                                                                                 (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                 (=>
                                                                                    (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                    (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     (not _$2_6)
                                                                     (let
                                                                        ((_$2_7 (< .0$2_0_old 100)))
                                                                        (=>
                                                                           _$2_7
                                                                           (let
                                                                              ((_$2_8 (+ result.0$2_0_old 1)))
                                                                              (let
                                                                                 ((retval.3$2_0 _$2_8)
                                                                                  (b.3$2_0 0)
                                                                                  (result.3$2_0 result.0$2_0_old)
                                                                                  (.3$2_0 .0$2_0_old))
                                                                                 (let
                                                                                    ((retval.4$2_0 retval.3$2_0)
                                                                                     (b.4$2_0 b.3$2_0)
                                                                                     (result.4$2_0 result.3$2_0)
                                                                                     (.4$2_0 .3$2_0))
                                                                                    (let
                                                                                       ((retval.0$2_0 retval.4$2_0)
                                                                                        (b.0$2_0 b.4$2_0)
                                                                                        (result.0$2_0 result.4$2_0)
                                                                                        (.0$2_0 .4$2_0))
                                                                                       (forall
                                                                                          ((result$1 Int)
                                                                                           (result$2 Int))
                                                                                          (and
                                                                                             (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                             (=>
                                                                                                (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                                (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     (not _$2_6)
                                                                     (let
                                                                        ((_$2_7 (< .0$2_0_old 100)))
                                                                        (=>
                                                                           (not _$2_7)
                                                                           (let
                                                                              ((_$2_9 (< .0$2_0_old 1000)))
                                                                              (=>
                                                                                 _$2_9
                                                                                 (let
                                                                                    ((_$2_10 (+ result.0$2_0_old 2)))
                                                                                    (let
                                                                                       ((retval.2$2_0 _$2_10)
                                                                                        (b.2$2_0 0)
                                                                                        (result.2$2_0 result.0$2_0_old)
                                                                                        (.2$2_0 .0$2_0_old))
                                                                                       (let
                                                                                          ((retval.3$2_0 retval.2$2_0)
                                                                                           (b.3$2_0 b.2$2_0)
                                                                                           (result.3$2_0 result.2$2_0)
                                                                                           (.3$2_0 .2$2_0))
                                                                                          (let
                                                                                             ((retval.4$2_0 retval.3$2_0)
                                                                                              (b.4$2_0 b.3$2_0)
                                                                                              (result.4$2_0 result.3$2_0)
                                                                                              (.4$2_0 .3$2_0))
                                                                                             (let
                                                                                                ((retval.0$2_0 retval.4$2_0)
                                                                                                 (b.0$2_0 b.4$2_0)
                                                                                                 (result.0$2_0 result.4$2_0)
                                                                                                 (.0$2_0 .4$2_0))
                                                                                                (forall
                                                                                                   ((result$1 Int)
                                                                                                    (result$2 Int))
                                                                                                   (and
                                                                                                      (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                                      (=>
                                                                                                         (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                                         (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     (not _$2_6)
                                                                     (let
                                                                        ((_$2_7 (< .0$2_0_old 100)))
                                                                        (=>
                                                                           (not _$2_7)
                                                                           (let
                                                                              ((_$2_9 (< .0$2_0_old 1000)))
                                                                              (=>
                                                                                 (not _$2_9)
                                                                                 (let
                                                                                    ((_$2_11 (< .0$2_0_old 10000)))
                                                                                    (=>
                                                                                       _$2_11
                                                                                       (let
                                                                                          ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                          (let
                                                                                             ((retval.1$2_0 _$2_12)
                                                                                              (b.1$2_0 0)
                                                                                              (result.1$2_0 result.0$2_0_old)
                                                                                              (.1$2_0 .0$2_0_old))
                                                                                             (let
                                                                                                ((retval.2$2_0 retval.1$2_0)
                                                                                                 (b.2$2_0 b.1$2_0)
                                                                                                 (result.2$2_0 result.1$2_0)
                                                                                                 (.2$2_0 .1$2_0))
                                                                                                (let
                                                                                                   ((retval.3$2_0 retval.2$2_0)
                                                                                                    (b.3$2_0 b.2$2_0)
                                                                                                    (result.3$2_0 result.2$2_0)
                                                                                                    (.3$2_0 .2$2_0))
                                                                                                   (let
                                                                                                      ((retval.4$2_0 retval.3$2_0)
                                                                                                       (b.4$2_0 b.3$2_0)
                                                                                                       (result.4$2_0 result.3$2_0)
                                                                                                       (.4$2_0 .3$2_0))
                                                                                                      (let
                                                                                                         ((retval.0$2_0 retval.4$2_0)
                                                                                                          (b.0$2_0 b.4$2_0)
                                                                                                          (result.0$2_0 result.4$2_0)
                                                                                                          (.0$2_0 .4$2_0))
                                                                                                         (forall
                                                                                                            ((result$1 Int)
                                                                                                             (result$2 Int))
                                                                                                            (and
                                                                                                               (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                                               (=>
                                                                                                                  (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                                                  (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0)
                                                          (_$2_1 (= b.0$2_0_old 0)))
                                                         (let
                                                            ((_$2_2 (xor
                                                                _$2_1
                                                                true)))
                                                            (=>
                                                               _$2_2
                                                               (let
                                                                  ((_$2_6 (< .0$2_0_old 10)))
                                                                  (=>
                                                                     (not _$2_6)
                                                                     (let
                                                                        ((_$2_7 (< .0$2_0_old 100)))
                                                                        (=>
                                                                           (not _$2_7)
                                                                           (let
                                                                              ((_$2_9 (< .0$2_0_old 1000)))
                                                                              (=>
                                                                                 (not _$2_9)
                                                                                 (let
                                                                                    ((_$2_11 (< .0$2_0_old 10000)))
                                                                                    (=>
                                                                                       (not _$2_11)
                                                                                       (let
                                                                                          ((_$2_13 (div
                                                                                              .0$2_0_old
                                                                                              10000))
                                                                                           (_$2_14 (+ result.0$2_0_old 4)))
                                                                                          (let
                                                                                             ((retval.1$2_0 retval.0$2_0_old)
                                                                                              (b.1$2_0 b.0$2_0_old)
                                                                                              (result.1$2_0 _$2_14)
                                                                                              (.1$2_0 _$2_13))
                                                                                             (let
                                                                                                ((retval.2$2_0 retval.1$2_0)
                                                                                                 (b.2$2_0 b.1$2_0)
                                                                                                 (result.2$2_0 result.1$2_0)
                                                                                                 (.2$2_0 .1$2_0))
                                                                                                (let
                                                                                                   ((retval.3$2_0 retval.2$2_0)
                                                                                                    (b.3$2_0 b.2$2_0)
                                                                                                    (result.3$2_0 result.2$2_0)
                                                                                                    (.3$2_0 .2$2_0))
                                                                                                   (let
                                                                                                      ((retval.4$2_0 retval.3$2_0)
                                                                                                       (b.4$2_0 b.3$2_0)
                                                                                                       (result.4$2_0 result.3$2_0)
                                                                                                       (.4$2_0 .3$2_0))
                                                                                                      (let
                                                                                                         ((retval.0$2_0 retval.4$2_0)
                                                                                                          (b.0$2_0 b.4$2_0)
                                                                                                          (result.0$2_0 result.4$2_0)
                                                                                                          (.0$2_0 .4$2_0))
                                                                                                         (forall
                                                                                                            ((result$1 Int)
                                                                                                             (result$2 Int))
                                                                                                            (and
                                                                                                               (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                                               (=>
                                                                                                                  (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                                                  (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  _$2_6
                                                                  (let
                                                                     ((retval.4$2_0 result.0$2_0_old)
                                                                      (b.4$2_0 0)
                                                                      (result.4$2_0 result.0$2_0_old)
                                                                      (.4$2_0 .0$2_0_old))
                                                                     (let
                                                                        ((retval.0$2_0 retval.4$2_0)
                                                                         (b.0$2_0 b.4$2_0)
                                                                         (result.0$2_0 result.4$2_0)
                                                                         (.0$2_0 .4$2_0))
                                                                        (forall
                                                                           ((result$1 Int)
                                                                            (result$2 Int))
                                                                           (and
                                                                              (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                              (=>
                                                                                 (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                 (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  (not _$2_6)
                                                                  (let
                                                                     ((_$2_7 (< .0$2_0_old 100)))
                                                                     (=>
                                                                        _$2_7
                                                                        (let
                                                                           ((_$2_8 (+ result.0$2_0_old 1)))
                                                                           (let
                                                                              ((retval.3$2_0 _$2_8)
                                                                               (b.3$2_0 0)
                                                                               (result.3$2_0 result.0$2_0_old)
                                                                               (.3$2_0 .0$2_0_old))
                                                                              (let
                                                                                 ((retval.4$2_0 retval.3$2_0)
                                                                                  (b.4$2_0 b.3$2_0)
                                                                                  (result.4$2_0 result.3$2_0)
                                                                                  (.4$2_0 .3$2_0))
                                                                                 (let
                                                                                    ((retval.0$2_0 retval.4$2_0)
                                                                                     (b.0$2_0 b.4$2_0)
                                                                                     (result.0$2_0 result.4$2_0)
                                                                                     (.0$2_0 .4$2_0))
                                                                                    (forall
                                                                                       ((result$1 Int)
                                                                                        (result$2 Int))
                                                                                       (and
                                                                                          (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                          (=>
                                                                                             (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                             (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  (not _$2_6)
                                                                  (let
                                                                     ((_$2_7 (< .0$2_0_old 100)))
                                                                     (=>
                                                                        (not _$2_7)
                                                                        (let
                                                                           ((_$2_9 (< .0$2_0_old 1000)))
                                                                           (=>
                                                                              _$2_9
                                                                              (let
                                                                                 ((_$2_10 (+ result.0$2_0_old 2)))
                                                                                 (let
                                                                                    ((retval.2$2_0 _$2_10)
                                                                                     (b.2$2_0 0)
                                                                                     (result.2$2_0 result.0$2_0_old)
                                                                                     (.2$2_0 .0$2_0_old))
                                                                                    (let
                                                                                       ((retval.3$2_0 retval.2$2_0)
                                                                                        (b.3$2_0 b.2$2_0)
                                                                                        (result.3$2_0 result.2$2_0)
                                                                                        (.3$2_0 .2$2_0))
                                                                                       (let
                                                                                          ((retval.4$2_0 retval.3$2_0)
                                                                                           (b.4$2_0 b.3$2_0)
                                                                                           (result.4$2_0 result.3$2_0)
                                                                                           (.4$2_0 .3$2_0))
                                                                                          (let
                                                                                             ((retval.0$2_0 retval.4$2_0)
                                                                                              (b.0$2_0 b.4$2_0)
                                                                                              (result.0$2_0 result.4$2_0)
                                                                                              (.0$2_0 .4$2_0))
                                                                                             (forall
                                                                                                ((result$1 Int)
                                                                                                 (result$2 Int))
                                                                                                (and
                                                                                                   (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                                   (=>
                                                                                                      (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                                      (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  (not _$2_6)
                                                                  (let
                                                                     ((_$2_7 (< .0$2_0_old 100)))
                                                                     (=>
                                                                        (not _$2_7)
                                                                        (let
                                                                           ((_$2_9 (< .0$2_0_old 1000)))
                                                                           (=>
                                                                              (not _$2_9)
                                                                              (let
                                                                                 ((_$2_11 (< .0$2_0_old 10000)))
                                                                                 (=>
                                                                                    _$2_11
                                                                                    (let
                                                                                       ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                       (let
                                                                                          ((retval.1$2_0 _$2_12)
                                                                                           (b.1$2_0 0)
                                                                                           (result.1$2_0 result.0$2_0_old)
                                                                                           (.1$2_0 .0$2_0_old))
                                                                                          (let
                                                                                             ((retval.2$2_0 retval.1$2_0)
                                                                                              (b.2$2_0 b.1$2_0)
                                                                                              (result.2$2_0 result.1$2_0)
                                                                                              (.2$2_0 .1$2_0))
                                                                                             (let
                                                                                                ((retval.3$2_0 retval.2$2_0)
                                                                                                 (b.3$2_0 b.2$2_0)
                                                                                                 (result.3$2_0 result.2$2_0)
                                                                                                 (.3$2_0 .2$2_0))
                                                                                                (let
                                                                                                   ((retval.4$2_0 retval.3$2_0)
                                                                                                    (b.4$2_0 b.3$2_0)
                                                                                                    (result.4$2_0 result.3$2_0)
                                                                                                    (.4$2_0 .3$2_0))
                                                                                                   (let
                                                                                                      ((retval.0$2_0 retval.4$2_0)
                                                                                                       (b.0$2_0 b.4$2_0)
                                                                                                       (result.0$2_0 result.4$2_0)
                                                                                                       (.0$2_0 .4$2_0))
                                                                                                      (forall
                                                                                                         ((result$1 Int)
                                                                                                          (result$2 Int))
                                                                                                         (and
                                                                                                            (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                                            (=>
                                                                                                               (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                                               (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0)
                                                       (_$2_1 (= b.0$2_0_old 0)))
                                                      (let
                                                         ((_$2_2 (xor
                                                             _$2_1
                                                             true)))
                                                         (=>
                                                            _$2_2
                                                            (let
                                                               ((_$2_6 (< .0$2_0_old 10)))
                                                               (=>
                                                                  (not _$2_6)
                                                                  (let
                                                                     ((_$2_7 (< .0$2_0_old 100)))
                                                                     (=>
                                                                        (not _$2_7)
                                                                        (let
                                                                           ((_$2_9 (< .0$2_0_old 1000)))
                                                                           (=>
                                                                              (not _$2_9)
                                                                              (let
                                                                                 ((_$2_11 (< .0$2_0_old 10000)))
                                                                                 (=>
                                                                                    (not _$2_11)
                                                                                    (let
                                                                                       ((_$2_13 (div
                                                                                           .0$2_0_old
                                                                                           10000))
                                                                                        (_$2_14 (+ result.0$2_0_old 4)))
                                                                                       (let
                                                                                          ((retval.1$2_0 retval.0$2_0_old)
                                                                                           (b.1$2_0 b.0$2_0_old)
                                                                                           (result.1$2_0 _$2_14)
                                                                                           (.1$2_0 _$2_13))
                                                                                          (let
                                                                                             ((retval.2$2_0 retval.1$2_0)
                                                                                              (b.2$2_0 b.1$2_0)
                                                                                              (result.2$2_0 result.1$2_0)
                                                                                              (.2$2_0 .1$2_0))
                                                                                             (let
                                                                                                ((retval.3$2_0 retval.2$2_0)
                                                                                                 (b.3$2_0 b.2$2_0)
                                                                                                 (result.3$2_0 result.2$2_0)
                                                                                                 (.3$2_0 .2$2_0))
                                                                                                (let
                                                                                                   ((retval.4$2_0 retval.3$2_0)
                                                                                                    (b.4$2_0 b.3$2_0)
                                                                                                    (result.4$2_0 result.3$2_0)
                                                                                                    (.4$2_0 .3$2_0))
                                                                                                   (let
                                                                                                      ((retval.0$2_0 retval.4$2_0)
                                                                                                       (b.0$2_0 b.4$2_0)
                                                                                                       (result.0$2_0 result.4$2_0)
                                                                                                       (.0$2_0 .4$2_0))
                                                                                                      (forall
                                                                                                         ((result$1 Int)
                                                                                                          (result$2 Int))
                                                                                                         (and
                                                                                                            (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                                            (=>
                                                                                                               (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                                               (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      _$2_6
                                                      (let
                                                         ((retval.4$2_0 result.0$2_0_old)
                                                          (b.4$2_0 0)
                                                          (result.4$2_0 result.0$2_0_old)
                                                          (.4$2_0 .0$2_0_old))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (forall
                                                               ((result$1 Int)
                                                                (result$2 Int))
                                                               (and
                                                                  (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                  (=>
                                                                     (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                     (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      (not _$2_6)
                                                      (let
                                                         ((_$2_7 (< .0$2_0_old 100)))
                                                         (=>
                                                            _$2_7
                                                            (let
                                                               ((_$2_8 (+ result.0$2_0_old 1)))
                                                               (let
                                                                  ((retval.3$2_0 _$2_8)
                                                                   (b.3$2_0 0)
                                                                   (result.3$2_0 result.0$2_0_old)
                                                                   (.3$2_0 .0$2_0_old))
                                                                  (let
                                                                     ((retval.4$2_0 retval.3$2_0)
                                                                      (b.4$2_0 b.3$2_0)
                                                                      (result.4$2_0 result.3$2_0)
                                                                      (.4$2_0 .3$2_0))
                                                                     (let
                                                                        ((retval.0$2_0 retval.4$2_0)
                                                                         (b.0$2_0 b.4$2_0)
                                                                         (result.0$2_0 result.4$2_0)
                                                                         (.0$2_0 .4$2_0))
                                                                        (forall
                                                                           ((result$1 Int)
                                                                            (result$2 Int))
                                                                           (and
                                                                              (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                              (=>
                                                                                 (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                 (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      (not _$2_6)
                                                      (let
                                                         ((_$2_7 (< .0$2_0_old 100)))
                                                         (=>
                                                            (not _$2_7)
                                                            (let
                                                               ((_$2_9 (< .0$2_0_old 1000)))
                                                               (=>
                                                                  _$2_9
                                                                  (let
                                                                     ((_$2_10 (+ result.0$2_0_old 2)))
                                                                     (let
                                                                        ((retval.2$2_0 _$2_10)
                                                                         (b.2$2_0 0)
                                                                         (result.2$2_0 result.0$2_0_old)
                                                                         (.2$2_0 .0$2_0_old))
                                                                        (let
                                                                           ((retval.3$2_0 retval.2$2_0)
                                                                            (b.3$2_0 b.2$2_0)
                                                                            (result.3$2_0 result.2$2_0)
                                                                            (.3$2_0 .2$2_0))
                                                                           (let
                                                                              ((retval.4$2_0 retval.3$2_0)
                                                                               (b.4$2_0 b.3$2_0)
                                                                               (result.4$2_0 result.3$2_0)
                                                                               (.4$2_0 .3$2_0))
                                                                              (let
                                                                                 ((retval.0$2_0 retval.4$2_0)
                                                                                  (b.0$2_0 b.4$2_0)
                                                                                  (result.0$2_0 result.4$2_0)
                                                                                  (.0$2_0 .4$2_0))
                                                                                 (forall
                                                                                    ((result$1 Int)
                                                                                     (result$2 Int))
                                                                                    (and
                                                                                       (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                       (=>
                                                                                          (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                          (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      (not _$2_6)
                                                      (let
                                                         ((_$2_7 (< .0$2_0_old 100)))
                                                         (=>
                                                            (not _$2_7)
                                                            (let
                                                               ((_$2_9 (< .0$2_0_old 1000)))
                                                               (=>
                                                                  (not _$2_9)
                                                                  (let
                                                                     ((_$2_11 (< .0$2_0_old 10000)))
                                                                     (=>
                                                                        _$2_11
                                                                        (let
                                                                           ((_$2_12 (+ result.0$2_0_old 3)))
                                                                           (let
                                                                              ((retval.1$2_0 _$2_12)
                                                                               (b.1$2_0 0)
                                                                               (result.1$2_0 result.0$2_0_old)
                                                                               (.1$2_0 .0$2_0_old))
                                                                              (let
                                                                                 ((retval.2$2_0 retval.1$2_0)
                                                                                  (b.2$2_0 b.1$2_0)
                                                                                  (result.2$2_0 result.1$2_0)
                                                                                  (.2$2_0 .1$2_0))
                                                                                 (let
                                                                                    ((retval.3$2_0 retval.2$2_0)
                                                                                     (b.3$2_0 b.2$2_0)
                                                                                     (result.3$2_0 result.2$2_0)
                                                                                     (.3$2_0 .2$2_0))
                                                                                    (let
                                                                                       ((retval.4$2_0 retval.3$2_0)
                                                                                        (b.4$2_0 b.3$2_0)
                                                                                        (result.4$2_0 result.3$2_0)
                                                                                        (.4$2_0 .3$2_0))
                                                                                       (let
                                                                                          ((retval.0$2_0 retval.4$2_0)
                                                                                           (b.0$2_0 b.4$2_0)
                                                                                           (result.0$2_0 result.4$2_0)
                                                                                           (.0$2_0 .4$2_0))
                                                                                          (forall
                                                                                             ((result$1 Int)
                                                                                              (result$2 Int))
                                                                                             (and
                                                                                                (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                                (=>
                                                                                                   (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                                   (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0)
                                           (_$2_1 (= b.0$2_0_old 0)))
                                          (let
                                             ((_$2_2 (xor
                                                 _$2_1
                                                 true)))
                                             (=>
                                                _$2_2
                                                (let
                                                   ((_$2_6 (< .0$2_0_old 10)))
                                                   (=>
                                                      (not _$2_6)
                                                      (let
                                                         ((_$2_7 (< .0$2_0_old 100)))
                                                         (=>
                                                            (not _$2_7)
                                                            (let
                                                               ((_$2_9 (< .0$2_0_old 1000)))
                                                               (=>
                                                                  (not _$2_9)
                                                                  (let
                                                                     ((_$2_11 (< .0$2_0_old 10000)))
                                                                     (=>
                                                                        (not _$2_11)
                                                                        (let
                                                                           ((_$2_13 (div
                                                                               .0$2_0_old
                                                                               10000))
                                                                            (_$2_14 (+ result.0$2_0_old 4)))
                                                                           (let
                                                                              ((retval.1$2_0 retval.0$2_0_old)
                                                                               (b.1$2_0 b.0$2_0_old)
                                                                               (result.1$2_0 _$2_14)
                                                                               (.1$2_0 _$2_13))
                                                                              (let
                                                                                 ((retval.2$2_0 retval.1$2_0)
                                                                                  (b.2$2_0 b.1$2_0)
                                                                                  (result.2$2_0 result.1$2_0)
                                                                                  (.2$2_0 .1$2_0))
                                                                                 (let
                                                                                    ((retval.3$2_0 retval.2$2_0)
                                                                                     (b.3$2_0 b.2$2_0)
                                                                                     (result.3$2_0 result.2$2_0)
                                                                                     (.3$2_0 .2$2_0))
                                                                                    (let
                                                                                       ((retval.4$2_0 retval.3$2_0)
                                                                                        (b.4$2_0 b.3$2_0)
                                                                                        (result.4$2_0 result.3$2_0)
                                                                                        (.4$2_0 .3$2_0))
                                                                                       (let
                                                                                          ((retval.0$2_0 retval.4$2_0)
                                                                                           (b.0$2_0 b.4$2_0)
                                                                                           (result.0$2_0 result.4$2_0)
                                                                                           (.0$2_0 .4$2_0))
                                                                                          (forall
                                                                                             ((result$1 Int)
                                                                                              (result$2 Int))
                                                                                             (and
                                                                                                (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                                (=>
                                                                                                   (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                                   (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          _$2_6
                                          (let
                                             ((retval.4$2_0 result.0$2_0_old)
                                              (b.4$2_0 0)
                                              (result.4$2_0 result.0$2_0_old)
                                              (.4$2_0 .0$2_0_old))
                                             (let
                                                ((retval.0$2_0 retval.4$2_0)
                                                 (b.0$2_0 b.4$2_0)
                                                 (result.0$2_0 result.4$2_0)
                                                 (.0$2_0 .4$2_0))
                                                (forall
                                                   ((result$1 Int)
                                                    (result$2 Int))
                                                   (and
                                                      (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                      (=>
                                                         (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                         (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          (not _$2_6)
                                          (let
                                             ((_$2_7 (< .0$2_0_old 100)))
                                             (=>
                                                _$2_7
                                                (let
                                                   ((_$2_8 (+ result.0$2_0_old 1)))
                                                   (let
                                                      ((retval.3$2_0 _$2_8)
                                                       (b.3$2_0 0)
                                                       (result.3$2_0 result.0$2_0_old)
                                                       (.3$2_0 .0$2_0_old))
                                                      (let
                                                         ((retval.4$2_0 retval.3$2_0)
                                                          (b.4$2_0 b.3$2_0)
                                                          (result.4$2_0 result.3$2_0)
                                                          (.4$2_0 .3$2_0))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (forall
                                                               ((result$1 Int)
                                                                (result$2 Int))
                                                               (and
                                                                  (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                  (=>
                                                                     (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                     (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          (not _$2_6)
                                          (let
                                             ((_$2_7 (< .0$2_0_old 100)))
                                             (=>
                                                (not _$2_7)
                                                (let
                                                   ((_$2_9 (< .0$2_0_old 1000)))
                                                   (=>
                                                      _$2_9
                                                      (let
                                                         ((_$2_10 (+ result.0$2_0_old 2)))
                                                         (let
                                                            ((retval.2$2_0 _$2_10)
                                                             (b.2$2_0 0)
                                                             (result.2$2_0 result.0$2_0_old)
                                                             (.2$2_0 .0$2_0_old))
                                                            (let
                                                               ((retval.3$2_0 retval.2$2_0)
                                                                (b.3$2_0 b.2$2_0)
                                                                (result.3$2_0 result.2$2_0)
                                                                (.3$2_0 .2$2_0))
                                                               (let
                                                                  ((retval.4$2_0 retval.3$2_0)
                                                                   (b.4$2_0 b.3$2_0)
                                                                   (result.4$2_0 result.3$2_0)
                                                                   (.4$2_0 .3$2_0))
                                                                  (let
                                                                     ((retval.0$2_0 retval.4$2_0)
                                                                      (b.0$2_0 b.4$2_0)
                                                                      (result.0$2_0 result.4$2_0)
                                                                      (.0$2_0 .4$2_0))
                                                                     (forall
                                                                        ((result$1 Int)
                                                                         (result$2 Int))
                                                                        (and
                                                                           (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                           (=>
                                                                              (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                              (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          (not _$2_6)
                                          (let
                                             ((_$2_7 (< .0$2_0_old 100)))
                                             (=>
                                                (not _$2_7)
                                                (let
                                                   ((_$2_9 (< .0$2_0_old 1000)))
                                                   (=>
                                                      (not _$2_9)
                                                      (let
                                                         ((_$2_11 (< .0$2_0_old 10000)))
                                                         (=>
                                                            _$2_11
                                                            (let
                                                               ((_$2_12 (+ result.0$2_0_old 3)))
                                                               (let
                                                                  ((retval.1$2_0 _$2_12)
                                                                   (b.1$2_0 0)
                                                                   (result.1$2_0 result.0$2_0_old)
                                                                   (.1$2_0 .0$2_0_old))
                                                                  (let
                                                                     ((retval.2$2_0 retval.1$2_0)
                                                                      (b.2$2_0 b.1$2_0)
                                                                      (result.2$2_0 result.1$2_0)
                                                                      (.2$2_0 .1$2_0))
                                                                     (let
                                                                        ((retval.3$2_0 retval.2$2_0)
                                                                         (b.3$2_0 b.2$2_0)
                                                                         (result.3$2_0 result.2$2_0)
                                                                         (.3$2_0 .2$2_0))
                                                                        (let
                                                                           ((retval.4$2_0 retval.3$2_0)
                                                                            (b.4$2_0 b.3$2_0)
                                                                            (result.4$2_0 result.3$2_0)
                                                                            (.4$2_0 .3$2_0))
                                                                           (let
                                                                              ((retval.0$2_0 retval.4$2_0)
                                                                               (b.0$2_0 b.4$2_0)
                                                                               (result.0$2_0 result.4$2_0)
                                                                               (.0$2_0 .4$2_0))
                                                                              (forall
                                                                                 ((result$1 Int)
                                                                                  (result$2 Int))
                                                                                 (and
                                                                                    (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                    (=>
                                                                                       (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                       (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0)
                               (_$2_1 (= b.0$2_0_old 0)))
                              (let
                                 ((_$2_2 (xor
                                     _$2_1
                                     true)))
                                 (=>
                                    _$2_2
                                    (let
                                       ((_$2_6 (< .0$2_0_old 10)))
                                       (=>
                                          (not _$2_6)
                                          (let
                                             ((_$2_7 (< .0$2_0_old 100)))
                                             (=>
                                                (not _$2_7)
                                                (let
                                                   ((_$2_9 (< .0$2_0_old 1000)))
                                                   (=>
                                                      (not _$2_9)
                                                      (let
                                                         ((_$2_11 (< .0$2_0_old 10000)))
                                                         (=>
                                                            (not _$2_11)
                                                            (let
                                                               ((_$2_13 (div
                                                                   .0$2_0_old
                                                                   10000))
                                                                (_$2_14 (+ result.0$2_0_old 4)))
                                                               (let
                                                                  ((retval.1$2_0 retval.0$2_0_old)
                                                                   (b.1$2_0 b.0$2_0_old)
                                                                   (result.1$2_0 _$2_14)
                                                                   (.1$2_0 _$2_13))
                                                                  (let
                                                                     ((retval.2$2_0 retval.1$2_0)
                                                                      (b.2$2_0 b.1$2_0)
                                                                      (result.2$2_0 result.1$2_0)
                                                                      (.2$2_0 .1$2_0))
                                                                     (let
                                                                        ((retval.3$2_0 retval.2$2_0)
                                                                         (b.3$2_0 b.2$2_0)
                                                                         (result.3$2_0 result.2$2_0)
                                                                         (.3$2_0 .2$2_0))
                                                                        (let
                                                                           ((retval.4$2_0 retval.3$2_0)
                                                                            (b.4$2_0 b.3$2_0)
                                                                            (result.4$2_0 result.3$2_0)
                                                                            (.4$2_0 .3$2_0))
                                                                           (let
                                                                              ((retval.0$2_0 retval.4$2_0)
                                                                               (b.0$2_0 b.4$2_0)
                                                                               (result.0$2_0 result.4$2_0)
                                                                               (.0$2_0 .4$2_0))
                                                                              (forall
                                                                                 ((result$1 Int)
                                                                                  (result$2 Int))
                                                                                 (and
                                                                                    (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                                    (=>
                                                                                       (INV_42 .0$1_0 result.0$1_0 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                                       (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE n$1_0_old)
         (let
            ((_$1_0 (div
                n$1_0_old
                10)))
            (let
               ((result.0$1_0 1)
                (.0$1_0 _$1_0))
               (forall
                  ((result$1 Int))
                  (=>
                     (INV_42__1 .0$1_0 result.0$1_0 result$1)
                     (INV_REC_f__1 n$1_0_old result$1))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int))
      (=>
         (INV_42__1_PRE .0$1_0_old result.0$1_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               (not _$1_2)
               (let
                  ((result$1 result.0$1_0_old))
                  (INV_42__1 .0$1_0_old result.0$1_0_old result$1)))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int))
      (=>
         (INV_42__1_PRE .0$1_0_old result.0$1_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0))
                                                         (forall
                                                            ((result$1 Int))
                                                            (=>
                                                               (INV_42__1 .0$1_0 result.0$1_0 result$1)
                                                               (INV_42__1 .0$1_0_old result.0$1_0_old result$1))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int))
      (=>
         (INV_42__1_PRE .0$1_0_old result.0$1_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0))
                                                      (forall
                                                         ((result$1 Int))
                                                         (=>
                                                            (INV_42__1 .0$1_0 result.0$1_0 result$1)
                                                            (INV_42__1 .0$1_0_old result.0$1_0_old result$1)))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int))
      (=>
         (INV_42__1_PRE .0$1_0_old result.0$1_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0))
                                          (forall
                                             ((result$1 Int))
                                             (=>
                                                (INV_42__1 .0$1_0 result.0$1_0 result$1)
                                                (INV_42__1 .0$1_0_old result.0$1_0_old result$1)))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int))
      (=>
         (INV_42__1_PRE .0$1_0_old result.0$1_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0))
                              (forall
                                 ((result$1 Int))
                                 (=>
                                    (INV_42__1 .0$1_0 result.0$1_0 result$1)
                                    (INV_42__1 .0$1_0_old result.0$1_0_old result$1)))))))))))))
(assert
   (forall
      ((n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE n$2_0_old)
         (let
            ((retval.0$2_0 (- 1))
             (b.0$2_0 1)
             (result.0$2_0 1)
             (.0$2_0 n$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_42__2 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$2)
                  (INV_REC_f__2 n$2_0_old result$2)))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  (not _$2_2)
                  (let
                     ((result$2 retval.0$2_0_old))
                     (INV_42__2 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$2))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        _$2_6
                        (let
                           ((retval.4$2_0 result.0$2_0_old)
                            (b.4$2_0 0)
                            (result.4$2_0 result.0$2_0_old)
                            (.4$2_0 .0$2_0_old))
                           (let
                              ((retval.0$2_0 retval.4$2_0)
                               (b.0$2_0 b.4$2_0)
                               (result.0$2_0 result.4$2_0)
                               (.0$2_0 .4$2_0))
                              (forall
                                 ((result$2 Int))
                                 (=>
                                    (INV_42__2 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$2)
                                    (INV_42__2 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$2)))))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              _$2_7
                              (let
                                 ((_$2_8 (+ result.0$2_0_old 1)))
                                 (let
                                    ((retval.3$2_0 _$2_8)
                                     (b.3$2_0 0)
                                     (result.3$2_0 result.0$2_0_old)
                                     (.3$2_0 .0$2_0_old))
                                    (let
                                       ((retval.4$2_0 retval.3$2_0)
                                        (b.4$2_0 b.3$2_0)
                                        (result.4$2_0 result.3$2_0)
                                        (.4$2_0 .3$2_0))
                                       (let
                                          ((retval.0$2_0 retval.4$2_0)
                                           (b.0$2_0 b.4$2_0)
                                           (result.0$2_0 result.4$2_0)
                                           (.0$2_0 .4$2_0))
                                          (forall
                                             ((result$2 Int))
                                             (=>
                                                (INV_42__2 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$2)
                                                (INV_42__2 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$2)))))))))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((_$2_9 (< .0$2_0_old 1000)))
                                 (=>
                                    _$2_9
                                    (let
                                       ((_$2_10 (+ result.0$2_0_old 2)))
                                       (let
                                          ((retval.2$2_0 _$2_10)
                                           (b.2$2_0 0)
                                           (result.2$2_0 result.0$2_0_old)
                                           (.2$2_0 .0$2_0_old))
                                          (let
                                             ((retval.3$2_0 retval.2$2_0)
                                              (b.3$2_0 b.2$2_0)
                                              (result.3$2_0 result.2$2_0)
                                              (.3$2_0 .2$2_0))
                                             (let
                                                ((retval.4$2_0 retval.3$2_0)
                                                 (b.4$2_0 b.3$2_0)
                                                 (result.4$2_0 result.3$2_0)
                                                 (.4$2_0 .3$2_0))
                                                (let
                                                   ((retval.0$2_0 retval.4$2_0)
                                                    (b.0$2_0 b.4$2_0)
                                                    (result.0$2_0 result.4$2_0)
                                                    (.0$2_0 .4$2_0))
                                                   (forall
                                                      ((result$2 Int))
                                                      (=>
                                                         (INV_42__2 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$2)
                                                         (INV_42__2 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$2))))))))))))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((_$2_9 (< .0$2_0_old 1000)))
                                 (=>
                                    (not _$2_9)
                                    (let
                                       ((_$2_11 (< .0$2_0_old 10000)))
                                       (=>
                                          _$2_11
                                          (let
                                             ((_$2_12 (+ result.0$2_0_old 3)))
                                             (let
                                                ((retval.1$2_0 _$2_12)
                                                 (b.1$2_0 0)
                                                 (result.1$2_0 result.0$2_0_old)
                                                 (.1$2_0 .0$2_0_old))
                                                (let
                                                   ((retval.2$2_0 retval.1$2_0)
                                                    (b.2$2_0 b.1$2_0)
                                                    (result.2$2_0 result.1$2_0)
                                                    (.2$2_0 .1$2_0))
                                                   (let
                                                      ((retval.3$2_0 retval.2$2_0)
                                                       (b.3$2_0 b.2$2_0)
                                                       (result.3$2_0 result.2$2_0)
                                                       (.3$2_0 .2$2_0))
                                                      (let
                                                         ((retval.4$2_0 retval.3$2_0)
                                                          (b.4$2_0 b.3$2_0)
                                                          (result.4$2_0 result.3$2_0)
                                                          (.4$2_0 .3$2_0))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (forall
                                                               ((result$2 Int))
                                                               (=>
                                                                  (INV_42__2 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$2)
                                                                  (INV_42__2 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$2)))))))))))))))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((_$2_9 (< .0$2_0_old 1000)))
                                 (=>
                                    (not _$2_9)
                                    (let
                                       ((_$2_11 (< .0$2_0_old 10000)))
                                       (=>
                                          (not _$2_11)
                                          (let
                                             ((_$2_13 (div
                                                 .0$2_0_old
                                                 10000))
                                              (_$2_14 (+ result.0$2_0_old 4)))
                                             (let
                                                ((retval.1$2_0 retval.0$2_0_old)
                                                 (b.1$2_0 b.0$2_0_old)
                                                 (result.1$2_0 _$2_14)
                                                 (.1$2_0 _$2_13))
                                                (let
                                                   ((retval.2$2_0 retval.1$2_0)
                                                    (b.2$2_0 b.1$2_0)
                                                    (result.2$2_0 result.1$2_0)
                                                    (.2$2_0 .1$2_0))
                                                   (let
                                                      ((retval.3$2_0 retval.2$2_0)
                                                       (b.3$2_0 b.2$2_0)
                                                       (result.3$2_0 result.2$2_0)
                                                       (.3$2_0 .2$2_0))
                                                      (let
                                                         ((retval.4$2_0 retval.3$2_0)
                                                          (b.4$2_0 b.3$2_0)
                                                          (result.4$2_0 result.3$2_0)
                                                          (.4$2_0 .3$2_0))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (forall
                                                               ((result$2 Int))
                                                               (=>
                                                                  (INV_42__2 .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$2)
                                                                  (INV_42__2 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$2)))))))))))))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          _$1_14
                                          (let
                                             ((_$1_15 (+ _$1_12 1))
                                              (_$1_16 (div
                                                 _$1_13
                                                 10)))
                                             (let
                                                ((result.1$1_0 _$1_15)
                                                 (.1$1_0 _$1_16))
                                                (let
                                                   ((result.2$1_0 result.1$1_0)
                                                    (.2$1_0 .1$1_0))
                                                   (let
                                                      ((result.3$1_0 result.2$1_0)
                                                       (.3$1_0 .2$1_0))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0))
                                                         (=>
                                                            (and
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              _$2_6
                                                                              (let
                                                                                 ((retval.4$2_0 result.0$2_0_old)
                                                                                  (b.4$2_0 0)
                                                                                  (result.4$2_0 result.0$2_0_old)
                                                                                  (.4$2_0 .0$2_0_old))
                                                                                 (let
                                                                                    ((retval.0$2_0 retval.4$2_0)
                                                                                     (b.0$2_0 b.4$2_0)
                                                                                     (result.0$2_0 result.4$2_0)
                                                                                     (.0$2_0 .4$2_0))
                                                                                    false)))))))
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              (not _$2_6)
                                                                              (let
                                                                                 ((_$2_7 (< .0$2_0_old 100)))
                                                                                 (=>
                                                                                    _$2_7
                                                                                    (let
                                                                                       ((_$2_8 (+ result.0$2_0_old 1)))
                                                                                       (let
                                                                                          ((retval.3$2_0 _$2_8)
                                                                                           (b.3$2_0 0)
                                                                                           (result.3$2_0 result.0$2_0_old)
                                                                                           (.3$2_0 .0$2_0_old))
                                                                                          (let
                                                                                             ((retval.4$2_0 retval.3$2_0)
                                                                                              (b.4$2_0 b.3$2_0)
                                                                                              (result.4$2_0 result.3$2_0)
                                                                                              (.4$2_0 .3$2_0))
                                                                                             (let
                                                                                                ((retval.0$2_0 retval.4$2_0)
                                                                                                 (b.0$2_0 b.4$2_0)
                                                                                                 (result.0$2_0 result.4$2_0)
                                                                                                 (.0$2_0 .4$2_0))
                                                                                                false)))))))))))
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              (not _$2_6)
                                                                              (let
                                                                                 ((_$2_7 (< .0$2_0_old 100)))
                                                                                 (=>
                                                                                    (not _$2_7)
                                                                                    (let
                                                                                       ((_$2_9 (< .0$2_0_old 1000)))
                                                                                       (=>
                                                                                          _$2_9
                                                                                          (let
                                                                                             ((_$2_10 (+ result.0$2_0_old 2)))
                                                                                             (let
                                                                                                ((retval.2$2_0 _$2_10)
                                                                                                 (b.2$2_0 0)
                                                                                                 (result.2$2_0 result.0$2_0_old)
                                                                                                 (.2$2_0 .0$2_0_old))
                                                                                                (let
                                                                                                   ((retval.3$2_0 retval.2$2_0)
                                                                                                    (b.3$2_0 b.2$2_0)
                                                                                                    (result.3$2_0 result.2$2_0)
                                                                                                    (.3$2_0 .2$2_0))
                                                                                                   (let
                                                                                                      ((retval.4$2_0 retval.3$2_0)
                                                                                                       (b.4$2_0 b.3$2_0)
                                                                                                       (result.4$2_0 result.3$2_0)
                                                                                                       (.4$2_0 .3$2_0))
                                                                                                      (let
                                                                                                         ((retval.0$2_0 retval.4$2_0)
                                                                                                          (b.0$2_0 b.4$2_0)
                                                                                                          (result.0$2_0 result.4$2_0)
                                                                                                          (.0$2_0 .4$2_0))
                                                                                                         false))))))))))))))
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              (not _$2_6)
                                                                              (let
                                                                                 ((_$2_7 (< .0$2_0_old 100)))
                                                                                 (=>
                                                                                    (not _$2_7)
                                                                                    (let
                                                                                       ((_$2_9 (< .0$2_0_old 1000)))
                                                                                       (=>
                                                                                          (not _$2_9)
                                                                                          (let
                                                                                             ((_$2_11 (< .0$2_0_old 10000)))
                                                                                             (=>
                                                                                                _$2_11
                                                                                                (let
                                                                                                   ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                                   (let
                                                                                                      ((retval.1$2_0 _$2_12)
                                                                                                       (b.1$2_0 0)
                                                                                                       (result.1$2_0 result.0$2_0_old)
                                                                                                       (.1$2_0 .0$2_0_old))
                                                                                                      (let
                                                                                                         ((retval.2$2_0 retval.1$2_0)
                                                                                                          (b.2$2_0 b.1$2_0)
                                                                                                          (result.2$2_0 result.1$2_0)
                                                                                                          (.2$2_0 .1$2_0))
                                                                                                         (let
                                                                                                            ((retval.3$2_0 retval.2$2_0)
                                                                                                             (b.3$2_0 b.2$2_0)
                                                                                                             (result.3$2_0 result.2$2_0)
                                                                                                             (.3$2_0 .2$2_0))
                                                                                                            (let
                                                                                                               ((retval.4$2_0 retval.3$2_0)
                                                                                                                (b.4$2_0 b.3$2_0)
                                                                                                                (result.4$2_0 result.3$2_0)
                                                                                                                (.4$2_0 .3$2_0))
                                                                                                               (let
                                                                                                                  ((retval.0$2_0 retval.4$2_0)
                                                                                                                   (b.0$2_0 b.4$2_0)
                                                                                                                   (result.0$2_0 result.4$2_0)
                                                                                                                   (.0$2_0 .4$2_0))
                                                                                                                  false)))))))))))))))))
                                                               (let
                                                                  ((_$2_1 (= b.0$2_0_old 0)))
                                                                  (let
                                                                     ((_$2_2 (xor
                                                                         _$2_1
                                                                         true)))
                                                                     (=>
                                                                        _$2_2
                                                                        (let
                                                                           ((_$2_6 (< .0$2_0_old 10)))
                                                                           (=>
                                                                              (not _$2_6)
                                                                              (let
                                                                                 ((_$2_7 (< .0$2_0_old 100)))
                                                                                 (=>
                                                                                    (not _$2_7)
                                                                                    (let
                                                                                       ((_$2_9 (< .0$2_0_old 1000)))
                                                                                       (=>
                                                                                          (not _$2_9)
                                                                                          (let
                                                                                             ((_$2_11 (< .0$2_0_old 10000)))
                                                                                             (=>
                                                                                                (not _$2_11)
                                                                                                (let
                                                                                                   ((_$2_13 (div
                                                                                                       .0$2_0_old
                                                                                                       10000))
                                                                                                    (_$2_14 (+ result.0$2_0_old 4)))
                                                                                                   (let
                                                                                                      ((retval.1$2_0 retval.0$2_0_old)
                                                                                                       (b.1$2_0 b.0$2_0_old)
                                                                                                       (result.1$2_0 _$2_14)
                                                                                                       (.1$2_0 _$2_13))
                                                                                                      (let
                                                                                                         ((retval.2$2_0 retval.1$2_0)
                                                                                                          (b.2$2_0 b.1$2_0)
                                                                                                          (result.2$2_0 result.1$2_0)
                                                                                                          (.2$2_0 .1$2_0))
                                                                                                         (let
                                                                                                            ((retval.3$2_0 retval.2$2_0)
                                                                                                             (b.3$2_0 b.2$2_0)
                                                                                                             (result.3$2_0 result.2$2_0)
                                                                                                             (.3$2_0 .2$2_0))
                                                                                                            (let
                                                                                                               ((retval.4$2_0 retval.3$2_0)
                                                                                                                (b.4$2_0 b.3$2_0)
                                                                                                                (result.4$2_0 result.3$2_0)
                                                                                                                (.4$2_0 .3$2_0))
                                                                                                               (let
                                                                                                                  ((retval.0$2_0 retval.4$2_0)
                                                                                                                   (b.0$2_0 b.4$2_0)
                                                                                                                   (result.0$2_0 result.4$2_0)
                                                                                                                   (.0$2_0 .4$2_0))
                                                                                                                  false))))))))))))))))))
                                                            (forall
                                                               ((result$1 Int)
                                                                (result$2 Int))
                                                               (and
                                                                  (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
                                                                  (=>
                                                                     (INV_42 .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)
                                                                     (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 _$1_11
                                 (let
                                    ((_$1_12 (+ _$1_9 1))
                                     (_$1_13 (div
                                        _$1_10
                                        10)))
                                    (let
                                       ((_$1_14 (> _$1_13 0)))
                                       (=>
                                          (not _$1_14)
                                          (let
                                             ((result.1$1_0 _$1_12)
                                              (.1$1_0 _$1_13))
                                             (let
                                                ((result.2$1_0 result.1$1_0)
                                                 (.2$1_0 .1$1_0))
                                                (let
                                                   ((result.3$1_0 result.2$1_0)
                                                    (.3$1_0 .2$1_0))
                                                   (let
                                                      ((result.0$1_0 result.3$1_0)
                                                       (.0$1_0 .3$1_0))
                                                      (=>
                                                         (and
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           _$2_6
                                                                           (let
                                                                              ((retval.4$2_0 result.0$2_0_old)
                                                                               (b.4$2_0 0)
                                                                               (result.4$2_0 result.0$2_0_old)
                                                                               (.4$2_0 .0$2_0_old))
                                                                              (let
                                                                                 ((retval.0$2_0 retval.4$2_0)
                                                                                  (b.0$2_0 b.4$2_0)
                                                                                  (result.0$2_0 result.4$2_0)
                                                                                  (.0$2_0 .4$2_0))
                                                                                 false)))))))
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           (not _$2_6)
                                                                           (let
                                                                              ((_$2_7 (< .0$2_0_old 100)))
                                                                              (=>
                                                                                 _$2_7
                                                                                 (let
                                                                                    ((_$2_8 (+ result.0$2_0_old 1)))
                                                                                    (let
                                                                                       ((retval.3$2_0 _$2_8)
                                                                                        (b.3$2_0 0)
                                                                                        (result.3$2_0 result.0$2_0_old)
                                                                                        (.3$2_0 .0$2_0_old))
                                                                                       (let
                                                                                          ((retval.4$2_0 retval.3$2_0)
                                                                                           (b.4$2_0 b.3$2_0)
                                                                                           (result.4$2_0 result.3$2_0)
                                                                                           (.4$2_0 .3$2_0))
                                                                                          (let
                                                                                             ((retval.0$2_0 retval.4$2_0)
                                                                                              (b.0$2_0 b.4$2_0)
                                                                                              (result.0$2_0 result.4$2_0)
                                                                                              (.0$2_0 .4$2_0))
                                                                                             false)))))))))))
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           (not _$2_6)
                                                                           (let
                                                                              ((_$2_7 (< .0$2_0_old 100)))
                                                                              (=>
                                                                                 (not _$2_7)
                                                                                 (let
                                                                                    ((_$2_9 (< .0$2_0_old 1000)))
                                                                                    (=>
                                                                                       _$2_9
                                                                                       (let
                                                                                          ((_$2_10 (+ result.0$2_0_old 2)))
                                                                                          (let
                                                                                             ((retval.2$2_0 _$2_10)
                                                                                              (b.2$2_0 0)
                                                                                              (result.2$2_0 result.0$2_0_old)
                                                                                              (.2$2_0 .0$2_0_old))
                                                                                             (let
                                                                                                ((retval.3$2_0 retval.2$2_0)
                                                                                                 (b.3$2_0 b.2$2_0)
                                                                                                 (result.3$2_0 result.2$2_0)
                                                                                                 (.3$2_0 .2$2_0))
                                                                                                (let
                                                                                                   ((retval.4$2_0 retval.3$2_0)
                                                                                                    (b.4$2_0 b.3$2_0)
                                                                                                    (result.4$2_0 result.3$2_0)
                                                                                                    (.4$2_0 .3$2_0))
                                                                                                   (let
                                                                                                      ((retval.0$2_0 retval.4$2_0)
                                                                                                       (b.0$2_0 b.4$2_0)
                                                                                                       (result.0$2_0 result.4$2_0)
                                                                                                       (.0$2_0 .4$2_0))
                                                                                                      false))))))))))))))
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           (not _$2_6)
                                                                           (let
                                                                              ((_$2_7 (< .0$2_0_old 100)))
                                                                              (=>
                                                                                 (not _$2_7)
                                                                                 (let
                                                                                    ((_$2_9 (< .0$2_0_old 1000)))
                                                                                    (=>
                                                                                       (not _$2_9)
                                                                                       (let
                                                                                          ((_$2_11 (< .0$2_0_old 10000)))
                                                                                          (=>
                                                                                             _$2_11
                                                                                             (let
                                                                                                ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                                (let
                                                                                                   ((retval.1$2_0 _$2_12)
                                                                                                    (b.1$2_0 0)
                                                                                                    (result.1$2_0 result.0$2_0_old)
                                                                                                    (.1$2_0 .0$2_0_old))
                                                                                                   (let
                                                                                                      ((retval.2$2_0 retval.1$2_0)
                                                                                                       (b.2$2_0 b.1$2_0)
                                                                                                       (result.2$2_0 result.1$2_0)
                                                                                                       (.2$2_0 .1$2_0))
                                                                                                      (let
                                                                                                         ((retval.3$2_0 retval.2$2_0)
                                                                                                          (b.3$2_0 b.2$2_0)
                                                                                                          (result.3$2_0 result.2$2_0)
                                                                                                          (.3$2_0 .2$2_0))
                                                                                                         (let
                                                                                                            ((retval.4$2_0 retval.3$2_0)
                                                                                                             (b.4$2_0 b.3$2_0)
                                                                                                             (result.4$2_0 result.3$2_0)
                                                                                                             (.4$2_0 .3$2_0))
                                                                                                            (let
                                                                                                               ((retval.0$2_0 retval.4$2_0)
                                                                                                                (b.0$2_0 b.4$2_0)
                                                                                                                (result.0$2_0 result.4$2_0)
                                                                                                                (.0$2_0 .4$2_0))
                                                                                                               false)))))))))))))))))
                                                            (let
                                                               ((_$2_1 (= b.0$2_0_old 0)))
                                                               (let
                                                                  ((_$2_2 (xor
                                                                      _$2_1
                                                                      true)))
                                                                  (=>
                                                                     _$2_2
                                                                     (let
                                                                        ((_$2_6 (< .0$2_0_old 10)))
                                                                        (=>
                                                                           (not _$2_6)
                                                                           (let
                                                                              ((_$2_7 (< .0$2_0_old 100)))
                                                                              (=>
                                                                                 (not _$2_7)
                                                                                 (let
                                                                                    ((_$2_9 (< .0$2_0_old 1000)))
                                                                                    (=>
                                                                                       (not _$2_9)
                                                                                       (let
                                                                                          ((_$2_11 (< .0$2_0_old 10000)))
                                                                                          (=>
                                                                                             (not _$2_11)
                                                                                             (let
                                                                                                ((_$2_13 (div
                                                                                                    .0$2_0_old
                                                                                                    10000))
                                                                                                 (_$2_14 (+ result.0$2_0_old 4)))
                                                                                                (let
                                                                                                   ((retval.1$2_0 retval.0$2_0_old)
                                                                                                    (b.1$2_0 b.0$2_0_old)
                                                                                                    (result.1$2_0 _$2_14)
                                                                                                    (.1$2_0 _$2_13))
                                                                                                   (let
                                                                                                      ((retval.2$2_0 retval.1$2_0)
                                                                                                       (b.2$2_0 b.1$2_0)
                                                                                                       (result.2$2_0 result.1$2_0)
                                                                                                       (.2$2_0 .1$2_0))
                                                                                                      (let
                                                                                                         ((retval.3$2_0 retval.2$2_0)
                                                                                                          (b.3$2_0 b.2$2_0)
                                                                                                          (result.3$2_0 result.2$2_0)
                                                                                                          (.3$2_0 .2$2_0))
                                                                                                         (let
                                                                                                            ((retval.4$2_0 retval.3$2_0)
                                                                                                             (b.4$2_0 b.3$2_0)
                                                                                                             (result.4$2_0 result.3$2_0)
                                                                                                             (.4$2_0 .3$2_0))
                                                                                                            (let
                                                                                                               ((retval.0$2_0 retval.4$2_0)
                                                                                                                (b.0$2_0 b.4$2_0)
                                                                                                                (result.0$2_0 result.4$2_0)
                                                                                                                (.0$2_0 .4$2_0))
                                                                                                               false))))))))))))))))))
                                                         (forall
                                                            ((result$1 Int)
                                                             (result$2 Int))
                                                            (and
                                                               (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
                                                               (=>
                                                                  (INV_42 .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)
                                                                  (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        _$1_8
                        (let
                           ((_$1_9 (+ _$1_6 1))
                            (_$1_10 (div
                               _$1_7
                               10)))
                           (let
                              ((_$1_11 (> _$1_10 0)))
                              (=>
                                 (not _$1_11)
                                 (let
                                    ((result.2$1_0 _$1_9)
                                     (.2$1_0 _$1_10))
                                    (let
                                       ((result.3$1_0 result.2$1_0)
                                        (.3$1_0 .2$1_0))
                                       (let
                                          ((result.0$1_0 result.3$1_0)
                                           (.0$1_0 .3$1_0))
                                          (=>
                                             (and
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               _$2_6
                                                               (let
                                                                  ((retval.4$2_0 result.0$2_0_old)
                                                                   (b.4$2_0 0)
                                                                   (result.4$2_0 result.0$2_0_old)
                                                                   (.4$2_0 .0$2_0_old))
                                                                  (let
                                                                     ((retval.0$2_0 retval.4$2_0)
                                                                      (b.0$2_0 b.4$2_0)
                                                                      (result.0$2_0 result.4$2_0)
                                                                      (.0$2_0 .4$2_0))
                                                                     false)))))))
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               (not _$2_6)
                                                               (let
                                                                  ((_$2_7 (< .0$2_0_old 100)))
                                                                  (=>
                                                                     _$2_7
                                                                     (let
                                                                        ((_$2_8 (+ result.0$2_0_old 1)))
                                                                        (let
                                                                           ((retval.3$2_0 _$2_8)
                                                                            (b.3$2_0 0)
                                                                            (result.3$2_0 result.0$2_0_old)
                                                                            (.3$2_0 .0$2_0_old))
                                                                           (let
                                                                              ((retval.4$2_0 retval.3$2_0)
                                                                               (b.4$2_0 b.3$2_0)
                                                                               (result.4$2_0 result.3$2_0)
                                                                               (.4$2_0 .3$2_0))
                                                                              (let
                                                                                 ((retval.0$2_0 retval.4$2_0)
                                                                                  (b.0$2_0 b.4$2_0)
                                                                                  (result.0$2_0 result.4$2_0)
                                                                                  (.0$2_0 .4$2_0))
                                                                                 false)))))))))))
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               (not _$2_6)
                                                               (let
                                                                  ((_$2_7 (< .0$2_0_old 100)))
                                                                  (=>
                                                                     (not _$2_7)
                                                                     (let
                                                                        ((_$2_9 (< .0$2_0_old 1000)))
                                                                        (=>
                                                                           _$2_9
                                                                           (let
                                                                              ((_$2_10 (+ result.0$2_0_old 2)))
                                                                              (let
                                                                                 ((retval.2$2_0 _$2_10)
                                                                                  (b.2$2_0 0)
                                                                                  (result.2$2_0 result.0$2_0_old)
                                                                                  (.2$2_0 .0$2_0_old))
                                                                                 (let
                                                                                    ((retval.3$2_0 retval.2$2_0)
                                                                                     (b.3$2_0 b.2$2_0)
                                                                                     (result.3$2_0 result.2$2_0)
                                                                                     (.3$2_0 .2$2_0))
                                                                                    (let
                                                                                       ((retval.4$2_0 retval.3$2_0)
                                                                                        (b.4$2_0 b.3$2_0)
                                                                                        (result.4$2_0 result.3$2_0)
                                                                                        (.4$2_0 .3$2_0))
                                                                                       (let
                                                                                          ((retval.0$2_0 retval.4$2_0)
                                                                                           (b.0$2_0 b.4$2_0)
                                                                                           (result.0$2_0 result.4$2_0)
                                                                                           (.0$2_0 .4$2_0))
                                                                                          false))))))))))))))
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               (not _$2_6)
                                                               (let
                                                                  ((_$2_7 (< .0$2_0_old 100)))
                                                                  (=>
                                                                     (not _$2_7)
                                                                     (let
                                                                        ((_$2_9 (< .0$2_0_old 1000)))
                                                                        (=>
                                                                           (not _$2_9)
                                                                           (let
                                                                              ((_$2_11 (< .0$2_0_old 10000)))
                                                                              (=>
                                                                                 _$2_11
                                                                                 (let
                                                                                    ((_$2_12 (+ result.0$2_0_old 3)))
                                                                                    (let
                                                                                       ((retval.1$2_0 _$2_12)
                                                                                        (b.1$2_0 0)
                                                                                        (result.1$2_0 result.0$2_0_old)
                                                                                        (.1$2_0 .0$2_0_old))
                                                                                       (let
                                                                                          ((retval.2$2_0 retval.1$2_0)
                                                                                           (b.2$2_0 b.1$2_0)
                                                                                           (result.2$2_0 result.1$2_0)
                                                                                           (.2$2_0 .1$2_0))
                                                                                          (let
                                                                                             ((retval.3$2_0 retval.2$2_0)
                                                                                              (b.3$2_0 b.2$2_0)
                                                                                              (result.3$2_0 result.2$2_0)
                                                                                              (.3$2_0 .2$2_0))
                                                                                             (let
                                                                                                ((retval.4$2_0 retval.3$2_0)
                                                                                                 (b.4$2_0 b.3$2_0)
                                                                                                 (result.4$2_0 result.3$2_0)
                                                                                                 (.4$2_0 .3$2_0))
                                                                                                (let
                                                                                                   ((retval.0$2_0 retval.4$2_0)
                                                                                                    (b.0$2_0 b.4$2_0)
                                                                                                    (result.0$2_0 result.4$2_0)
                                                                                                    (.0$2_0 .4$2_0))
                                                                                                   false)))))))))))))))))
                                                (let
                                                   ((_$2_1 (= b.0$2_0_old 0)))
                                                   (let
                                                      ((_$2_2 (xor
                                                          _$2_1
                                                          true)))
                                                      (=>
                                                         _$2_2
                                                         (let
                                                            ((_$2_6 (< .0$2_0_old 10)))
                                                            (=>
                                                               (not _$2_6)
                                                               (let
                                                                  ((_$2_7 (< .0$2_0_old 100)))
                                                                  (=>
                                                                     (not _$2_7)
                                                                     (let
                                                                        ((_$2_9 (< .0$2_0_old 1000)))
                                                                        (=>
                                                                           (not _$2_9)
                                                                           (let
                                                                              ((_$2_11 (< .0$2_0_old 10000)))
                                                                              (=>
                                                                                 (not _$2_11)
                                                                                 (let
                                                                                    ((_$2_13 (div
                                                                                        .0$2_0_old
                                                                                        10000))
                                                                                     (_$2_14 (+ result.0$2_0_old 4)))
                                                                                    (let
                                                                                       ((retval.1$2_0 retval.0$2_0_old)
                                                                                        (b.1$2_0 b.0$2_0_old)
                                                                                        (result.1$2_0 _$2_14)
                                                                                        (.1$2_0 _$2_13))
                                                                                       (let
                                                                                          ((retval.2$2_0 retval.1$2_0)
                                                                                           (b.2$2_0 b.1$2_0)
                                                                                           (result.2$2_0 result.1$2_0)
                                                                                           (.2$2_0 .1$2_0))
                                                                                          (let
                                                                                             ((retval.3$2_0 retval.2$2_0)
                                                                                              (b.3$2_0 b.2$2_0)
                                                                                              (result.3$2_0 result.2$2_0)
                                                                                              (.3$2_0 .2$2_0))
                                                                                             (let
                                                                                                ((retval.4$2_0 retval.3$2_0)
                                                                                                 (b.4$2_0 b.3$2_0)
                                                                                                 (result.4$2_0 result.3$2_0)
                                                                                                 (.4$2_0 .3$2_0))
                                                                                                (let
                                                                                                   ((retval.0$2_0 retval.4$2_0)
                                                                                                    (b.0$2_0 b.4$2_0)
                                                                                                    (result.0$2_0 result.4$2_0)
                                                                                                    (.0$2_0 .4$2_0))
                                                                                                   false))))))))))))))))))
                                             (forall
                                                ((result$1 Int)
                                                 (result$2 Int))
                                                (and
                                                   (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
                                                   (=>
                                                      (INV_42 .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)
                                                      (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$1_2 (> .0$1_0_old 0)))
            (=>
               _$1_2
               (let
                  ((_$1_6 (+ result.0$1_0_old 1))
                   (_$1_7 (div
                      .0$1_0_old
                      10)))
                  (let
                     ((_$1_8 (> _$1_7 0)))
                     (=>
                        (not _$1_8)
                        (let
                           ((result.3$1_0 _$1_6)
                            (.3$1_0 _$1_7))
                           (let
                              ((result.0$1_0 result.3$1_0)
                               (.0$1_0 .3$1_0))
                              (=>
                                 (and
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   _$2_6
                                                   (let
                                                      ((retval.4$2_0 result.0$2_0_old)
                                                       (b.4$2_0 0)
                                                       (result.4$2_0 result.0$2_0_old)
                                                       (.4$2_0 .0$2_0_old))
                                                      (let
                                                         ((retval.0$2_0 retval.4$2_0)
                                                          (b.0$2_0 b.4$2_0)
                                                          (result.0$2_0 result.4$2_0)
                                                          (.0$2_0 .4$2_0))
                                                         false)))))))
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   (not _$2_6)
                                                   (let
                                                      ((_$2_7 (< .0$2_0_old 100)))
                                                      (=>
                                                         _$2_7
                                                         (let
                                                            ((_$2_8 (+ result.0$2_0_old 1)))
                                                            (let
                                                               ((retval.3$2_0 _$2_8)
                                                                (b.3$2_0 0)
                                                                (result.3$2_0 result.0$2_0_old)
                                                                (.3$2_0 .0$2_0_old))
                                                               (let
                                                                  ((retval.4$2_0 retval.3$2_0)
                                                                   (b.4$2_0 b.3$2_0)
                                                                   (result.4$2_0 result.3$2_0)
                                                                   (.4$2_0 .3$2_0))
                                                                  (let
                                                                     ((retval.0$2_0 retval.4$2_0)
                                                                      (b.0$2_0 b.4$2_0)
                                                                      (result.0$2_0 result.4$2_0)
                                                                      (.0$2_0 .4$2_0))
                                                                     false)))))))))))
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   (not _$2_6)
                                                   (let
                                                      ((_$2_7 (< .0$2_0_old 100)))
                                                      (=>
                                                         (not _$2_7)
                                                         (let
                                                            ((_$2_9 (< .0$2_0_old 1000)))
                                                            (=>
                                                               _$2_9
                                                               (let
                                                                  ((_$2_10 (+ result.0$2_0_old 2)))
                                                                  (let
                                                                     ((retval.2$2_0 _$2_10)
                                                                      (b.2$2_0 0)
                                                                      (result.2$2_0 result.0$2_0_old)
                                                                      (.2$2_0 .0$2_0_old))
                                                                     (let
                                                                        ((retval.3$2_0 retval.2$2_0)
                                                                         (b.3$2_0 b.2$2_0)
                                                                         (result.3$2_0 result.2$2_0)
                                                                         (.3$2_0 .2$2_0))
                                                                        (let
                                                                           ((retval.4$2_0 retval.3$2_0)
                                                                            (b.4$2_0 b.3$2_0)
                                                                            (result.4$2_0 result.3$2_0)
                                                                            (.4$2_0 .3$2_0))
                                                                           (let
                                                                              ((retval.0$2_0 retval.4$2_0)
                                                                               (b.0$2_0 b.4$2_0)
                                                                               (result.0$2_0 result.4$2_0)
                                                                               (.0$2_0 .4$2_0))
                                                                              false))))))))))))))
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   (not _$2_6)
                                                   (let
                                                      ((_$2_7 (< .0$2_0_old 100)))
                                                      (=>
                                                         (not _$2_7)
                                                         (let
                                                            ((_$2_9 (< .0$2_0_old 1000)))
                                                            (=>
                                                               (not _$2_9)
                                                               (let
                                                                  ((_$2_11 (< .0$2_0_old 10000)))
                                                                  (=>
                                                                     _$2_11
                                                                     (let
                                                                        ((_$2_12 (+ result.0$2_0_old 3)))
                                                                        (let
                                                                           ((retval.1$2_0 _$2_12)
                                                                            (b.1$2_0 0)
                                                                            (result.1$2_0 result.0$2_0_old)
                                                                            (.1$2_0 .0$2_0_old))
                                                                           (let
                                                                              ((retval.2$2_0 retval.1$2_0)
                                                                               (b.2$2_0 b.1$2_0)
                                                                               (result.2$2_0 result.1$2_0)
                                                                               (.2$2_0 .1$2_0))
                                                                              (let
                                                                                 ((retval.3$2_0 retval.2$2_0)
                                                                                  (b.3$2_0 b.2$2_0)
                                                                                  (result.3$2_0 result.2$2_0)
                                                                                  (.3$2_0 .2$2_0))
                                                                                 (let
                                                                                    ((retval.4$2_0 retval.3$2_0)
                                                                                     (b.4$2_0 b.3$2_0)
                                                                                     (result.4$2_0 result.3$2_0)
                                                                                     (.4$2_0 .3$2_0))
                                                                                    (let
                                                                                       ((retval.0$2_0 retval.4$2_0)
                                                                                        (b.0$2_0 b.4$2_0)
                                                                                        (result.0$2_0 result.4$2_0)
                                                                                        (.0$2_0 .4$2_0))
                                                                                       false)))))))))))))))))
                                    (let
                                       ((_$2_1 (= b.0$2_0_old 0)))
                                       (let
                                          ((_$2_2 (xor
                                              _$2_1
                                              true)))
                                          (=>
                                             _$2_2
                                             (let
                                                ((_$2_6 (< .0$2_0_old 10)))
                                                (=>
                                                   (not _$2_6)
                                                   (let
                                                      ((_$2_7 (< .0$2_0_old 100)))
                                                      (=>
                                                         (not _$2_7)
                                                         (let
                                                            ((_$2_9 (< .0$2_0_old 1000)))
                                                            (=>
                                                               (not _$2_9)
                                                               (let
                                                                  ((_$2_11 (< .0$2_0_old 10000)))
                                                                  (=>
                                                                     (not _$2_11)
                                                                     (let
                                                                        ((_$2_13 (div
                                                                            .0$2_0_old
                                                                            10000))
                                                                         (_$2_14 (+ result.0$2_0_old 4)))
                                                                        (let
                                                                           ((retval.1$2_0 retval.0$2_0_old)
                                                                            (b.1$2_0 b.0$2_0_old)
                                                                            (result.1$2_0 _$2_14)
                                                                            (.1$2_0 _$2_13))
                                                                           (let
                                                                              ((retval.2$2_0 retval.1$2_0)
                                                                               (b.2$2_0 b.1$2_0)
                                                                               (result.2$2_0 result.1$2_0)
                                                                               (.2$2_0 .1$2_0))
                                                                              (let
                                                                                 ((retval.3$2_0 retval.2$2_0)
                                                                                  (b.3$2_0 b.2$2_0)
                                                                                  (result.3$2_0 result.2$2_0)
                                                                                  (.3$2_0 .2$2_0))
                                                                                 (let
                                                                                    ((retval.4$2_0 retval.3$2_0)
                                                                                     (b.4$2_0 b.3$2_0)
                                                                                     (result.4$2_0 result.3$2_0)
                                                                                     (.4$2_0 .3$2_0))
                                                                                    (let
                                                                                       ((retval.0$2_0 retval.4$2_0)
                                                                                        (b.0$2_0 b.4$2_0)
                                                                                        (result.0$2_0 result.4$2_0)
                                                                                        (.0$2_0 .4$2_0))
                                                                                       false))))))))))))))))))
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_42_PRE .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
                                       (=>
                                          (INV_42 .0$1_0 result.0$1_0 .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)
                                          (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        _$2_6
                        (let
                           ((retval.4$2_0 result.0$2_0_old)
                            (b.4$2_0 0)
                            (result.4$2_0 result.0$2_0_old)
                            (.4$2_0 .0$2_0_old))
                           (let
                              ((retval.0$2_0 retval.4$2_0)
                               (b.0$2_0 b.4$2_0)
                               (result.0$2_0 result.4$2_0)
                               (.0$2_0 .4$2_0))
                              (=>
                                 (and
                                    (let
                                       ((_$1_2 (> .0$1_0_old 0)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ result.0$1_0_old 1))
                                              (_$1_7 (div
                                                 .0$1_0_old
                                                 10)))
                                             (let
                                                ((_$1_8 (> _$1_7 0)))
                                                (=>
                                                   _$1_8
                                                   (let
                                                      ((_$1_9 (+ _$1_6 1))
                                                       (_$1_10 (div
                                                          _$1_7
                                                          10)))
                                                      (let
                                                         ((_$1_11 (> _$1_10 0)))
                                                         (=>
                                                            _$1_11
                                                            (let
                                                               ((_$1_12 (+ _$1_9 1))
                                                                (_$1_13 (div
                                                                   _$1_10
                                                                   10)))
                                                               (let
                                                                  ((_$1_14 (> _$1_13 0)))
                                                                  (=>
                                                                     _$1_14
                                                                     (let
                                                                        ((_$1_15 (+ _$1_12 1))
                                                                         (_$1_16 (div
                                                                            _$1_13
                                                                            10)))
                                                                        (let
                                                                           ((result.1$1_0 _$1_15)
                                                                            (.1$1_0 _$1_16))
                                                                           (let
                                                                              ((result.2$1_0 result.1$1_0)
                                                                               (.2$1_0 .1$1_0))
                                                                              (let
                                                                                 ((result.3$1_0 result.2$1_0)
                                                                                  (.3$1_0 .2$1_0))
                                                                                 (let
                                                                                    ((result.0$1_0 result.3$1_0)
                                                                                     (.0$1_0 .3$1_0))
                                                                                    false))))))))))))))))
                                    (let
                                       ((_$1_2 (> .0$1_0_old 0)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ result.0$1_0_old 1))
                                              (_$1_7 (div
                                                 .0$1_0_old
                                                 10)))
                                             (let
                                                ((_$1_8 (> _$1_7 0)))
                                                (=>
                                                   _$1_8
                                                   (let
                                                      ((_$1_9 (+ _$1_6 1))
                                                       (_$1_10 (div
                                                          _$1_7
                                                          10)))
                                                      (let
                                                         ((_$1_11 (> _$1_10 0)))
                                                         (=>
                                                            _$1_11
                                                            (let
                                                               ((_$1_12 (+ _$1_9 1))
                                                                (_$1_13 (div
                                                                   _$1_10
                                                                   10)))
                                                               (let
                                                                  ((_$1_14 (> _$1_13 0)))
                                                                  (=>
                                                                     (not _$1_14)
                                                                     (let
                                                                        ((result.1$1_0 _$1_12)
                                                                         (.1$1_0 _$1_13))
                                                                        (let
                                                                           ((result.2$1_0 result.1$1_0)
                                                                            (.2$1_0 .1$1_0))
                                                                           (let
                                                                              ((result.3$1_0 result.2$1_0)
                                                                               (.3$1_0 .2$1_0))
                                                                              (let
                                                                                 ((result.0$1_0 result.3$1_0)
                                                                                  (.0$1_0 .3$1_0))
                                                                                 false)))))))))))))))
                                    (let
                                       ((_$1_2 (> .0$1_0_old 0)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ result.0$1_0_old 1))
                                              (_$1_7 (div
                                                 .0$1_0_old
                                                 10)))
                                             (let
                                                ((_$1_8 (> _$1_7 0)))
                                                (=>
                                                   _$1_8
                                                   (let
                                                      ((_$1_9 (+ _$1_6 1))
                                                       (_$1_10 (div
                                                          _$1_7
                                                          10)))
                                                      (let
                                                         ((_$1_11 (> _$1_10 0)))
                                                         (=>
                                                            (not _$1_11)
                                                            (let
                                                               ((result.2$1_0 _$1_9)
                                                                (.2$1_0 _$1_10))
                                                               (let
                                                                  ((result.3$1_0 result.2$1_0)
                                                                   (.3$1_0 .2$1_0))
                                                                  (let
                                                                     ((result.0$1_0 result.3$1_0)
                                                                      (.0$1_0 .3$1_0))
                                                                     false)))))))))))
                                    (let
                                       ((_$1_2 (> .0$1_0_old 0)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((_$1_6 (+ result.0$1_0_old 1))
                                              (_$1_7 (div
                                                 .0$1_0_old
                                                 10)))
                                             (let
                                                ((_$1_8 (> _$1_7 0)))
                                                (=>
                                                   (not _$1_8)
                                                   (let
                                                      ((result.3$1_0 _$1_6)
                                                       (.3$1_0 _$1_7))
                                                      (let
                                                         ((result.0$1_0 result.3$1_0)
                                                          (.0$1_0 .3$1_0))
                                                         false))))))))
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                       (=>
                                          (INV_42 .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                          (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              _$2_7
                              (let
                                 ((_$2_8 (+ result.0$2_0_old 1)))
                                 (let
                                    ((retval.3$2_0 _$2_8)
                                     (b.3$2_0 0)
                                     (result.3$2_0 result.0$2_0_old)
                                     (.3$2_0 .0$2_0_old))
                                    (let
                                       ((retval.4$2_0 retval.3$2_0)
                                        (b.4$2_0 b.3$2_0)
                                        (result.4$2_0 result.3$2_0)
                                        (.4$2_0 .3$2_0))
                                       (let
                                          ((retval.0$2_0 retval.4$2_0)
                                           (b.0$2_0 b.4$2_0)
                                           (result.0$2_0 result.4$2_0)
                                           (.0$2_0 .4$2_0))
                                          (=>
                                             (and
                                                (let
                                                   ((_$1_2 (> .0$1_0_old 0)))
                                                   (=>
                                                      _$1_2
                                                      (let
                                                         ((_$1_6 (+ result.0$1_0_old 1))
                                                          (_$1_7 (div
                                                             .0$1_0_old
                                                             10)))
                                                         (let
                                                            ((_$1_8 (> _$1_7 0)))
                                                            (=>
                                                               _$1_8
                                                               (let
                                                                  ((_$1_9 (+ _$1_6 1))
                                                                   (_$1_10 (div
                                                                      _$1_7
                                                                      10)))
                                                                  (let
                                                                     ((_$1_11 (> _$1_10 0)))
                                                                     (=>
                                                                        _$1_11
                                                                        (let
                                                                           ((_$1_12 (+ _$1_9 1))
                                                                            (_$1_13 (div
                                                                               _$1_10
                                                                               10)))
                                                                           (let
                                                                              ((_$1_14 (> _$1_13 0)))
                                                                              (=>
                                                                                 _$1_14
                                                                                 (let
                                                                                    ((_$1_15 (+ _$1_12 1))
                                                                                     (_$1_16 (div
                                                                                        _$1_13
                                                                                        10)))
                                                                                    (let
                                                                                       ((result.1$1_0 _$1_15)
                                                                                        (.1$1_0 _$1_16))
                                                                                       (let
                                                                                          ((result.2$1_0 result.1$1_0)
                                                                                           (.2$1_0 .1$1_0))
                                                                                          (let
                                                                                             ((result.3$1_0 result.2$1_0)
                                                                                              (.3$1_0 .2$1_0))
                                                                                             (let
                                                                                                ((result.0$1_0 result.3$1_0)
                                                                                                 (.0$1_0 .3$1_0))
                                                                                                false))))))))))))))))
                                                (let
                                                   ((_$1_2 (> .0$1_0_old 0)))
                                                   (=>
                                                      _$1_2
                                                      (let
                                                         ((_$1_6 (+ result.0$1_0_old 1))
                                                          (_$1_7 (div
                                                             .0$1_0_old
                                                             10)))
                                                         (let
                                                            ((_$1_8 (> _$1_7 0)))
                                                            (=>
                                                               _$1_8
                                                               (let
                                                                  ((_$1_9 (+ _$1_6 1))
                                                                   (_$1_10 (div
                                                                      _$1_7
                                                                      10)))
                                                                  (let
                                                                     ((_$1_11 (> _$1_10 0)))
                                                                     (=>
                                                                        _$1_11
                                                                        (let
                                                                           ((_$1_12 (+ _$1_9 1))
                                                                            (_$1_13 (div
                                                                               _$1_10
                                                                               10)))
                                                                           (let
                                                                              ((_$1_14 (> _$1_13 0)))
                                                                              (=>
                                                                                 (not _$1_14)
                                                                                 (let
                                                                                    ((result.1$1_0 _$1_12)
                                                                                     (.1$1_0 _$1_13))
                                                                                    (let
                                                                                       ((result.2$1_0 result.1$1_0)
                                                                                        (.2$1_0 .1$1_0))
                                                                                       (let
                                                                                          ((result.3$1_0 result.2$1_0)
                                                                                           (.3$1_0 .2$1_0))
                                                                                          (let
                                                                                             ((result.0$1_0 result.3$1_0)
                                                                                              (.0$1_0 .3$1_0))
                                                                                             false)))))))))))))))
                                                (let
                                                   ((_$1_2 (> .0$1_0_old 0)))
                                                   (=>
                                                      _$1_2
                                                      (let
                                                         ((_$1_6 (+ result.0$1_0_old 1))
                                                          (_$1_7 (div
                                                             .0$1_0_old
                                                             10)))
                                                         (let
                                                            ((_$1_8 (> _$1_7 0)))
                                                            (=>
                                                               _$1_8
                                                               (let
                                                                  ((_$1_9 (+ _$1_6 1))
                                                                   (_$1_10 (div
                                                                      _$1_7
                                                                      10)))
                                                                  (let
                                                                     ((_$1_11 (> _$1_10 0)))
                                                                     (=>
                                                                        (not _$1_11)
                                                                        (let
                                                                           ((result.2$1_0 _$1_9)
                                                                            (.2$1_0 _$1_10))
                                                                           (let
                                                                              ((result.3$1_0 result.2$1_0)
                                                                               (.3$1_0 .2$1_0))
                                                                              (let
                                                                                 ((result.0$1_0 result.3$1_0)
                                                                                  (.0$1_0 .3$1_0))
                                                                                 false)))))))))))
                                                (let
                                                   ((_$1_2 (> .0$1_0_old 0)))
                                                   (=>
                                                      _$1_2
                                                      (let
                                                         ((_$1_6 (+ result.0$1_0_old 1))
                                                          (_$1_7 (div
                                                             .0$1_0_old
                                                             10)))
                                                         (let
                                                            ((_$1_8 (> _$1_7 0)))
                                                            (=>
                                                               (not _$1_8)
                                                               (let
                                                                  ((result.3$1_0 _$1_6)
                                                                   (.3$1_0 _$1_7))
                                                                  (let
                                                                     ((result.0$1_0 result.3$1_0)
                                                                      (.0$1_0 .3$1_0))
                                                                     false))))))))
                                             (forall
                                                ((result$1 Int)
                                                 (result$2 Int))
                                                (and
                                                   (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                   (=>
                                                      (INV_42 .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                      (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((_$2_9 (< .0$2_0_old 1000)))
                                 (=>
                                    _$2_9
                                    (let
                                       ((_$2_10 (+ result.0$2_0_old 2)))
                                       (let
                                          ((retval.2$2_0 _$2_10)
                                           (b.2$2_0 0)
                                           (result.2$2_0 result.0$2_0_old)
                                           (.2$2_0 .0$2_0_old))
                                          (let
                                             ((retval.3$2_0 retval.2$2_0)
                                              (b.3$2_0 b.2$2_0)
                                              (result.3$2_0 result.2$2_0)
                                              (.3$2_0 .2$2_0))
                                             (let
                                                ((retval.4$2_0 retval.3$2_0)
                                                 (b.4$2_0 b.3$2_0)
                                                 (result.4$2_0 result.3$2_0)
                                                 (.4$2_0 .3$2_0))
                                                (let
                                                   ((retval.0$2_0 retval.4$2_0)
                                                    (b.0$2_0 b.4$2_0)
                                                    (result.0$2_0 result.4$2_0)
                                                    (.0$2_0 .4$2_0))
                                                   (=>
                                                      (and
                                                         (let
                                                            ((_$1_2 (> .0$1_0_old 0)))
                                                            (=>
                                                               _$1_2
                                                               (let
                                                                  ((_$1_6 (+ result.0$1_0_old 1))
                                                                   (_$1_7 (div
                                                                      .0$1_0_old
                                                                      10)))
                                                                  (let
                                                                     ((_$1_8 (> _$1_7 0)))
                                                                     (=>
                                                                        _$1_8
                                                                        (let
                                                                           ((_$1_9 (+ _$1_6 1))
                                                                            (_$1_10 (div
                                                                               _$1_7
                                                                               10)))
                                                                           (let
                                                                              ((_$1_11 (> _$1_10 0)))
                                                                              (=>
                                                                                 _$1_11
                                                                                 (let
                                                                                    ((_$1_12 (+ _$1_9 1))
                                                                                     (_$1_13 (div
                                                                                        _$1_10
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_14 (> _$1_13 0)))
                                                                                       (=>
                                                                                          _$1_14
                                                                                          (let
                                                                                             ((_$1_15 (+ _$1_12 1))
                                                                                              (_$1_16 (div
                                                                                                 _$1_13
                                                                                                 10)))
                                                                                             (let
                                                                                                ((result.1$1_0 _$1_15)
                                                                                                 (.1$1_0 _$1_16))
                                                                                                (let
                                                                                                   ((result.2$1_0 result.1$1_0)
                                                                                                    (.2$1_0 .1$1_0))
                                                                                                   (let
                                                                                                      ((result.3$1_0 result.2$1_0)
                                                                                                       (.3$1_0 .2$1_0))
                                                                                                      (let
                                                                                                         ((result.0$1_0 result.3$1_0)
                                                                                                          (.0$1_0 .3$1_0))
                                                                                                         false))))))))))))))))
                                                         (let
                                                            ((_$1_2 (> .0$1_0_old 0)))
                                                            (=>
                                                               _$1_2
                                                               (let
                                                                  ((_$1_6 (+ result.0$1_0_old 1))
                                                                   (_$1_7 (div
                                                                      .0$1_0_old
                                                                      10)))
                                                                  (let
                                                                     ((_$1_8 (> _$1_7 0)))
                                                                     (=>
                                                                        _$1_8
                                                                        (let
                                                                           ((_$1_9 (+ _$1_6 1))
                                                                            (_$1_10 (div
                                                                               _$1_7
                                                                               10)))
                                                                           (let
                                                                              ((_$1_11 (> _$1_10 0)))
                                                                              (=>
                                                                                 _$1_11
                                                                                 (let
                                                                                    ((_$1_12 (+ _$1_9 1))
                                                                                     (_$1_13 (div
                                                                                        _$1_10
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_14 (> _$1_13 0)))
                                                                                       (=>
                                                                                          (not _$1_14)
                                                                                          (let
                                                                                             ((result.1$1_0 _$1_12)
                                                                                              (.1$1_0 _$1_13))
                                                                                             (let
                                                                                                ((result.2$1_0 result.1$1_0)
                                                                                                 (.2$1_0 .1$1_0))
                                                                                                (let
                                                                                                   ((result.3$1_0 result.2$1_0)
                                                                                                    (.3$1_0 .2$1_0))
                                                                                                   (let
                                                                                                      ((result.0$1_0 result.3$1_0)
                                                                                                       (.0$1_0 .3$1_0))
                                                                                                      false)))))))))))))))
                                                         (let
                                                            ((_$1_2 (> .0$1_0_old 0)))
                                                            (=>
                                                               _$1_2
                                                               (let
                                                                  ((_$1_6 (+ result.0$1_0_old 1))
                                                                   (_$1_7 (div
                                                                      .0$1_0_old
                                                                      10)))
                                                                  (let
                                                                     ((_$1_8 (> _$1_7 0)))
                                                                     (=>
                                                                        _$1_8
                                                                        (let
                                                                           ((_$1_9 (+ _$1_6 1))
                                                                            (_$1_10 (div
                                                                               _$1_7
                                                                               10)))
                                                                           (let
                                                                              ((_$1_11 (> _$1_10 0)))
                                                                              (=>
                                                                                 (not _$1_11)
                                                                                 (let
                                                                                    ((result.2$1_0 _$1_9)
                                                                                     (.2$1_0 _$1_10))
                                                                                    (let
                                                                                       ((result.3$1_0 result.2$1_0)
                                                                                        (.3$1_0 .2$1_0))
                                                                                       (let
                                                                                          ((result.0$1_0 result.3$1_0)
                                                                                           (.0$1_0 .3$1_0))
                                                                                          false)))))))))))
                                                         (let
                                                            ((_$1_2 (> .0$1_0_old 0)))
                                                            (=>
                                                               _$1_2
                                                               (let
                                                                  ((_$1_6 (+ result.0$1_0_old 1))
                                                                   (_$1_7 (div
                                                                      .0$1_0_old
                                                                      10)))
                                                                  (let
                                                                     ((_$1_8 (> _$1_7 0)))
                                                                     (=>
                                                                        (not _$1_8)
                                                                        (let
                                                                           ((result.3$1_0 _$1_6)
                                                                            (.3$1_0 _$1_7))
                                                                           (let
                                                                              ((result.0$1_0 result.3$1_0)
                                                                               (.0$1_0 .3$1_0))
                                                                              false))))))))
                                                      (forall
                                                         ((result$1 Int)
                                                          (result$2 Int))
                                                         (and
                                                            (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                            (=>
                                                               (INV_42 .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                               (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((_$2_9 (< .0$2_0_old 1000)))
                                 (=>
                                    (not _$2_9)
                                    (let
                                       ((_$2_11 (< .0$2_0_old 10000)))
                                       (=>
                                          _$2_11
                                          (let
                                             ((_$2_12 (+ result.0$2_0_old 3)))
                                             (let
                                                ((retval.1$2_0 _$2_12)
                                                 (b.1$2_0 0)
                                                 (result.1$2_0 result.0$2_0_old)
                                                 (.1$2_0 .0$2_0_old))
                                                (let
                                                   ((retval.2$2_0 retval.1$2_0)
                                                    (b.2$2_0 b.1$2_0)
                                                    (result.2$2_0 result.1$2_0)
                                                    (.2$2_0 .1$2_0))
                                                   (let
                                                      ((retval.3$2_0 retval.2$2_0)
                                                       (b.3$2_0 b.2$2_0)
                                                       (result.3$2_0 result.2$2_0)
                                                       (.3$2_0 .2$2_0))
                                                      (let
                                                         ((retval.4$2_0 retval.3$2_0)
                                                          (b.4$2_0 b.3$2_0)
                                                          (result.4$2_0 result.3$2_0)
                                                          (.4$2_0 .3$2_0))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (=>
                                                               (and
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          _$1_11
                                                                                          (let
                                                                                             ((_$1_12 (+ _$1_9 1))
                                                                                              (_$1_13 (div
                                                                                                 _$1_10
                                                                                                 10)))
                                                                                             (let
                                                                                                ((_$1_14 (> _$1_13 0)))
                                                                                                (=>
                                                                                                   _$1_14
                                                                                                   (let
                                                                                                      ((_$1_15 (+ _$1_12 1))
                                                                                                       (_$1_16 (div
                                                                                                          _$1_13
                                                                                                          10)))
                                                                                                      (let
                                                                                                         ((result.1$1_0 _$1_15)
                                                                                                          (.1$1_0 _$1_16))
                                                                                                         (let
                                                                                                            ((result.2$1_0 result.1$1_0)
                                                                                                             (.2$1_0 .1$1_0))
                                                                                                            (let
                                                                                                               ((result.3$1_0 result.2$1_0)
                                                                                                                (.3$1_0 .2$1_0))
                                                                                                               (let
                                                                                                                  ((result.0$1_0 result.3$1_0)
                                                                                                                   (.0$1_0 .3$1_0))
                                                                                                                  false))))))))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          _$1_11
                                                                                          (let
                                                                                             ((_$1_12 (+ _$1_9 1))
                                                                                              (_$1_13 (div
                                                                                                 _$1_10
                                                                                                 10)))
                                                                                             (let
                                                                                                ((_$1_14 (> _$1_13 0)))
                                                                                                (=>
                                                                                                   (not _$1_14)
                                                                                                   (let
                                                                                                      ((result.1$1_0 _$1_12)
                                                                                                       (.1$1_0 _$1_13))
                                                                                                      (let
                                                                                                         ((result.2$1_0 result.1$1_0)
                                                                                                          (.2$1_0 .1$1_0))
                                                                                                         (let
                                                                                                            ((result.3$1_0 result.2$1_0)
                                                                                                             (.3$1_0 .2$1_0))
                                                                                                            (let
                                                                                                               ((result.0$1_0 result.3$1_0)
                                                                                                                (.0$1_0 .3$1_0))
                                                                                                               false)))))))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          (not _$1_11)
                                                                                          (let
                                                                                             ((result.2$1_0 _$1_9)
                                                                                              (.2$1_0 _$1_10))
                                                                                             (let
                                                                                                ((result.3$1_0 result.2$1_0)
                                                                                                 (.3$1_0 .2$1_0))
                                                                                                (let
                                                                                                   ((result.0$1_0 result.3$1_0)
                                                                                                    (.0$1_0 .3$1_0))
                                                                                                   false)))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 (not _$1_8)
                                                                                 (let
                                                                                    ((result.3$1_0 _$1_6)
                                                                                     (.3$1_0 _$1_7))
                                                                                    (let
                                                                                       ((result.0$1_0 result.3$1_0)
                                                                                        (.0$1_0 .3$1_0))
                                                                                       false))))))))
                                                               (forall
                                                                  ((result$1 Int)
                                                                   (result$2 Int))
                                                                  (and
                                                                     (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                     (=>
                                                                        (INV_42 .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                        (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (result.0$1_0_old Int)
       (.0$2_0_old Int)
       (b.0$2_0_old Int)
       (result.0$2_0_old Int)
       (retval.0$2_0_old Int))
      (=>
         (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old)
         (let
            ((_$2_1 (= b.0$2_0_old 0)))
            (let
               ((_$2_2 (xor
                   _$2_1
                   true)))
               (=>
                  _$2_2
                  (let
                     ((_$2_6 (< .0$2_0_old 10)))
                     (=>
                        (not _$2_6)
                        (let
                           ((_$2_7 (< .0$2_0_old 100)))
                           (=>
                              (not _$2_7)
                              (let
                                 ((_$2_9 (< .0$2_0_old 1000)))
                                 (=>
                                    (not _$2_9)
                                    (let
                                       ((_$2_11 (< .0$2_0_old 10000)))
                                       (=>
                                          (not _$2_11)
                                          (let
                                             ((_$2_13 (div
                                                 .0$2_0_old
                                                 10000))
                                              (_$2_14 (+ result.0$2_0_old 4)))
                                             (let
                                                ((retval.1$2_0 retval.0$2_0_old)
                                                 (b.1$2_0 b.0$2_0_old)
                                                 (result.1$2_0 _$2_14)
                                                 (.1$2_0 _$2_13))
                                                (let
                                                   ((retval.2$2_0 retval.1$2_0)
                                                    (b.2$2_0 b.1$2_0)
                                                    (result.2$2_0 result.1$2_0)
                                                    (.2$2_0 .1$2_0))
                                                   (let
                                                      ((retval.3$2_0 retval.2$2_0)
                                                       (b.3$2_0 b.2$2_0)
                                                       (result.3$2_0 result.2$2_0)
                                                       (.3$2_0 .2$2_0))
                                                      (let
                                                         ((retval.4$2_0 retval.3$2_0)
                                                          (b.4$2_0 b.3$2_0)
                                                          (result.4$2_0 result.3$2_0)
                                                          (.4$2_0 .3$2_0))
                                                         (let
                                                            ((retval.0$2_0 retval.4$2_0)
                                                             (b.0$2_0 b.4$2_0)
                                                             (result.0$2_0 result.4$2_0)
                                                             (.0$2_0 .4$2_0))
                                                            (=>
                                                               (and
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          _$1_11
                                                                                          (let
                                                                                             ((_$1_12 (+ _$1_9 1))
                                                                                              (_$1_13 (div
                                                                                                 _$1_10
                                                                                                 10)))
                                                                                             (let
                                                                                                ((_$1_14 (> _$1_13 0)))
                                                                                                (=>
                                                                                                   _$1_14
                                                                                                   (let
                                                                                                      ((_$1_15 (+ _$1_12 1))
                                                                                                       (_$1_16 (div
                                                                                                          _$1_13
                                                                                                          10)))
                                                                                                      (let
                                                                                                         ((result.1$1_0 _$1_15)
                                                                                                          (.1$1_0 _$1_16))
                                                                                                         (let
                                                                                                            ((result.2$1_0 result.1$1_0)
                                                                                                             (.2$1_0 .1$1_0))
                                                                                                            (let
                                                                                                               ((result.3$1_0 result.2$1_0)
                                                                                                                (.3$1_0 .2$1_0))
                                                                                                               (let
                                                                                                                  ((result.0$1_0 result.3$1_0)
                                                                                                                   (.0$1_0 .3$1_0))
                                                                                                                  false))))))))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          _$1_11
                                                                                          (let
                                                                                             ((_$1_12 (+ _$1_9 1))
                                                                                              (_$1_13 (div
                                                                                                 _$1_10
                                                                                                 10)))
                                                                                             (let
                                                                                                ((_$1_14 (> _$1_13 0)))
                                                                                                (=>
                                                                                                   (not _$1_14)
                                                                                                   (let
                                                                                                      ((result.1$1_0 _$1_12)
                                                                                                       (.1$1_0 _$1_13))
                                                                                                      (let
                                                                                                         ((result.2$1_0 result.1$1_0)
                                                                                                          (.2$1_0 .1$1_0))
                                                                                                         (let
                                                                                                            ((result.3$1_0 result.2$1_0)
                                                                                                             (.3$1_0 .2$1_0))
                                                                                                            (let
                                                                                                               ((result.0$1_0 result.3$1_0)
                                                                                                                (.0$1_0 .3$1_0))
                                                                                                               false)))))))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 _$1_8
                                                                                 (let
                                                                                    ((_$1_9 (+ _$1_6 1))
                                                                                     (_$1_10 (div
                                                                                        _$1_7
                                                                                        10)))
                                                                                    (let
                                                                                       ((_$1_11 (> _$1_10 0)))
                                                                                       (=>
                                                                                          (not _$1_11)
                                                                                          (let
                                                                                             ((result.2$1_0 _$1_9)
                                                                                              (.2$1_0 _$1_10))
                                                                                             (let
                                                                                                ((result.3$1_0 result.2$1_0)
                                                                                                 (.3$1_0 .2$1_0))
                                                                                                (let
                                                                                                   ((result.0$1_0 result.3$1_0)
                                                                                                    (.0$1_0 .3$1_0))
                                                                                                   false)))))))))))
                                                                  (let
                                                                     ((_$1_2 (> .0$1_0_old 0)))
                                                                     (=>
                                                                        _$1_2
                                                                        (let
                                                                           ((_$1_6 (+ result.0$1_0_old 1))
                                                                            (_$1_7 (div
                                                                               .0$1_0_old
                                                                               10)))
                                                                           (let
                                                                              ((_$1_8 (> _$1_7 0)))
                                                                              (=>
                                                                                 (not _$1_8)
                                                                                 (let
                                                                                    ((result.3$1_0 _$1_6)
                                                                                     (.3$1_0 _$1_7))
                                                                                    (let
                                                                                       ((result.0$1_0 result.3$1_0)
                                                                                        (.0$1_0 .3$1_0))
                                                                                       false))))))))
                                                               (forall
                                                                  ((result$1 Int)
                                                                   (result$2 Int))
                                                                  (and
                                                                     (INV_42_PRE .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0)
                                                                     (=>
                                                                        (INV_42 .0$1_0_old result.0$1_0_old .0$2_0 b.0$2_0 result.0$2_0 retval.0$2_0 result$1 result$2)
                                                                        (INV_42 .0$1_0_old result.0$1_0_old .0$2_0_old b.0$2_0_old result.0$2_0_old retval.0$2_0_old result$1 result$2)))))))))))))))))))))))))
(check-sat)
(get-model)
