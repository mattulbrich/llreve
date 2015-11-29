(set-logic HORN)
(define-fun
   IN_INV
   ((sb$1_0 Int)
    (ancestors$1_0 Int)
    (sb$2_0 Int)
    (ancestors$2_0 Int))
   Bool
   (and
      (= sb$1_0 sb$2_0)
      (= ancestors$1_0 ancestors$2_0)))
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
   INV_REC_is_ancestor
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_is_ancestor_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_is_ancestor__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_is_ancestor__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_is_ancestor__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_is_ancestor__2_PRE
   (Int
    Int)
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
      ((sb$1_0_old Int)
       (ancestors$1_0_old Int)
       (sb$2_0_old Int)
       (ancestors$2_0_old Int))
      (=>
         (IN_INV
            sb$1_0_old
            ancestors$1_0_old
            sb$2_0_old
            ancestors$2_0_old)
         (let
            ((.01$1_0 ancestors$1_0_old)
             (sb$1_0 sb$1_0_old)
             (.01$2_0 ancestors$2_0_old)
             (sb$2_0 sb$2_0_old))
            (INV_42_MAIN .01$1_0 sb$1_0 .01$2_0 sb$2_0)))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             _$1_14
                                             (let
                                                ((.0$1_0 true))
                                                (let
                                                   ((result$1 .0$1_0)
                                                    (_$2_1 (distinct .01$2_0_old 0)))
                                                   (=>
                                                      _$2_1
                                                      (let
                                                         ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                         (let
                                                            ((_$2_6 (select HEAP$2_old _$2_5))
                                                             (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                            (let
                                                               ((_$2_8 (select HEAP$2_old _$2_7)))
                                                               (let
                                                                  ((_$2_9 (= _$2_6 _$2_8)))
                                                                  (=>
                                                                     _$2_9
                                                                     (let
                                                                        ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                                        (let
                                                                           ((_$2_11 (select HEAP$2_old _$2_10))
                                                                            (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                                           (let
                                                                              ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                              (let
                                                                                 ((_$2_14 (= _$2_11 _$2_13)))
                                                                                 (=>
                                                                                    _$2_14
                                                                                    (let
                                                                                       ((.0$2_0 true))
                                                                                       (let
                                                                                          ((result$2 .0$2_0))
                                                                                          (OUT_INV
                                                                                             result$1
                                                                                             result$2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             _$1_14
                                             (let
                                                ((.0$1_0 true))
                                                (let
                                                   ((result$1 .0$1_0)
                                                    (_$2_1 (distinct .01$2_0_old 0)))
                                                   (=>
                                                      (not _$2_1)
                                                      (let
                                                         ((.0$2_0 false))
                                                         (let
                                                            ((result$2 .0$2_0))
                                                            (OUT_INV
                                                               result$1
                                                               result$2)))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               (not _$1_1)
               (let
                  ((.0$1_0 false))
                  (let
                     ((result$1 .0$1_0)
                      (_$2_1 (distinct .01$2_0_old 0)))
                     (=>
                        _$2_1
                        (let
                           ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                           (let
                              ((_$2_6 (select HEAP$2_old _$2_5))
                               (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                              (let
                                 ((_$2_8 (select HEAP$2_old _$2_7)))
                                 (let
                                    ((_$2_9 (= _$2_6 _$2_8)))
                                    (=>
                                       _$2_9
                                       (let
                                          ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                          (let
                                             ((_$2_11 (select HEAP$2_old _$2_10))
                                              (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                             (let
                                                ((_$2_13 (select HEAP$2_old _$2_12)))
                                                (let
                                                   ((_$2_14 (= _$2_11 _$2_13)))
                                                   (=>
                                                      _$2_14
                                                      (let
                                                         ((.0$2_0 true))
                                                         (let
                                                            ((result$2 .0$2_0))
                                                            (OUT_INV
                                                               result$1
                                                               result$2)))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               (not _$1_1)
               (let
                  ((.0$1_0 false))
                  (let
                     ((result$1 .0$1_0)
                      (_$2_1 (distinct .01$2_0_old 0)))
                     (=>
                        (not _$2_1)
                        (let
                           ((.0$2_0 false))
                           (let
                              ((result$2 .0$2_0))
                              (OUT_INV
                                 result$1
                                 result$2)))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             (not _$1_14)
                                             (let
                                                ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$1_16 (select HEAP$1_old _$1_15)))
                                                   (let
                                                      ((.01$1_0 _$1_16)
                                                       (sb$1_0 sb$1_0_old)
                                                       (_$2_1 (distinct .01$2_0_old 0)))
                                                      (=>
                                                         _$2_1
                                                         (let
                                                            ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                            (let
                                                               ((_$2_6 (select HEAP$2_old _$2_5))
                                                                (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                               (let
                                                                  ((_$2_8 (select HEAP$2_old _$2_7)))
                                                                  (let
                                                                     ((_$2_9 (= _$2_6 _$2_8)))
                                                                     (=>
                                                                        _$2_9
                                                                        (let
                                                                           ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                                           (let
                                                                              ((_$2_11 (select HEAP$2_old _$2_10))
                                                                               (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                                              (let
                                                                                 ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                                 (let
                                                                                    ((_$2_14 (= _$2_11 _$2_13)))
                                                                                    (=>
                                                                                       (not _$2_14)
                                                                                       (let
                                                                                          ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                                          (let
                                                                                             ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                                             (let
                                                                                                ((.01$2_0 _$2_16)
                                                                                                 (sb$2_0 sb$2_0_old))
                                                                                                (INV_42_MAIN .01$1_0 sb$1_0 .01$2_0 sb$2_0)))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             (not _$1_14)
                                             (let
                                                ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$1_16 (select HEAP$1_old _$1_15)))
                                                   (let
                                                      ((.01$1_0 _$1_16)
                                                       (sb$1_0 sb$1_0_old)
                                                       (_$2_1 (distinct .01$2_0_old 0)))
                                                      (=>
                                                         _$2_1
                                                         (let
                                                            ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                            (let
                                                               ((_$2_6 (select HEAP$2_old _$2_5))
                                                                (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                               (let
                                                                  ((_$2_8 (select HEAP$2_old _$2_7)))
                                                                  (let
                                                                     ((_$2_9 (= _$2_6 _$2_8)))
                                                                     (=>
                                                                        (not _$2_9)
                                                                        (let
                                                                           ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                           (let
                                                                              ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                              (let
                                                                                 ((.01$2_0 _$2_16)
                                                                                  (sb$2_0 sb$2_0_old))
                                                                                 (INV_42_MAIN .01$1_0 sb$1_0 .01$2_0 sb$2_0))))))))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              (not _$1_9)
                              (let
                                 ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$1_16 (select HEAP$1_old _$1_15)))
                                    (let
                                       ((.01$1_0 _$1_16)
                                        (sb$1_0 sb$1_0_old)
                                        (_$2_1 (distinct .01$2_0_old 0)))
                                       (=>
                                          _$2_1
                                          (let
                                             ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                             (let
                                                ((_$2_6 (select HEAP$2_old _$2_5))
                                                 (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                (let
                                                   ((_$2_8 (select HEAP$2_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (= _$2_6 _$2_8)))
                                                      (=>
                                                         _$2_9
                                                         (let
                                                            ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                            (let
                                                               ((_$2_11 (select HEAP$2_old _$2_10))
                                                                (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                               (let
                                                                  ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                  (let
                                                                     ((_$2_14 (= _$2_11 _$2_13)))
                                                                     (=>
                                                                        (not _$2_14)
                                                                        (let
                                                                           ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                           (let
                                                                              ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                              (let
                                                                                 ((.01$2_0 _$2_16)
                                                                                  (sb$2_0 sb$2_0_old))
                                                                                 (INV_42_MAIN .01$1_0 sb$1_0 .01$2_0 sb$2_0))))))))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              (not _$1_9)
                              (let
                                 ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$1_16 (select HEAP$1_old _$1_15)))
                                    (let
                                       ((.01$1_0 _$1_16)
                                        (sb$1_0 sb$1_0_old)
                                        (_$2_1 (distinct .01$2_0_old 0)))
                                       (=>
                                          _$2_1
                                          (let
                                             ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                             (let
                                                ((_$2_6 (select HEAP$2_old _$2_5))
                                                 (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                (let
                                                   ((_$2_8 (select HEAP$2_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (= _$2_6 _$2_8)))
                                                      (=>
                                                         (not _$2_9)
                                                         (let
                                                            ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                            (let
                                                               ((_$2_16 (select HEAP$2_old _$2_15)))
                                                               (let
                                                                  ((.01$2_0 _$2_16)
                                                                   (sb$2_0 sb$2_0_old))
                                                                  (INV_42_MAIN .01$1_0 sb$1_0 .01$2_0 sb$2_0)))))))))))))))))))))))
; forbidden main
; offbyn main
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             (not _$1_14)
                                             (let
                                                ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$1_16 (select HEAP$1_old _$1_15)))
                                                   (let
                                                      ((.01$1_0 _$1_16)
                                                       (sb$1_0 sb$1_0_old))
                                                      (=>
                                                         (and
                                                            (let
                                                               ((_$2_1 (distinct .01$2_0_old 0)))
                                                               (=>
                                                                  _$2_1
                                                                  (let
                                                                     ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                                     (let
                                                                        ((_$2_6 (select HEAP$2_old _$2_5))
                                                                         (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                                        (let
                                                                           ((_$2_8 (select HEAP$2_old _$2_7)))
                                                                           (let
                                                                              ((_$2_9 (= _$2_6 _$2_8)))
                                                                              (=>
                                                                                 _$2_9
                                                                                 (let
                                                                                    ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                                                    (let
                                                                                       ((_$2_11 (select HEAP$2_old _$2_10))
                                                                                        (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                                                       (let
                                                                                          ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                                          (let
                                                                                             ((_$2_14 (= _$2_11 _$2_13)))
                                                                                             (=>
                                                                                                (not _$2_14)
                                                                                                (let
                                                                                                   ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                                                   (let
                                                                                                      ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                                                      (let
                                                                                                         ((.01$2_0 _$2_16)
                                                                                                          (sb$2_0 sb$2_0_old))
                                                                                                         false)))))))))))))))
                                                            (let
                                                               ((_$2_1 (distinct .01$2_0_old 0)))
                                                               (=>
                                                                  _$2_1
                                                                  (let
                                                                     ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                                     (let
                                                                        ((_$2_6 (select HEAP$2_old _$2_5))
                                                                         (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                                        (let
                                                                           ((_$2_8 (select HEAP$2_old _$2_7)))
                                                                           (let
                                                                              ((_$2_9 (= _$2_6 _$2_8)))
                                                                              (=>
                                                                                 (not _$2_9)
                                                                                 (let
                                                                                    ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                                    (let
                                                                                       ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                                       (let
                                                                                          ((.01$2_0 _$2_16)
                                                                                           (sb$2_0 sb$2_0_old))
                                                                                          false)))))))))))
                                                         (INV_42_MAIN .01$1_0 sb$1_0 .01$2_0_old sb$2_0_old))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              (not _$1_9)
                              (let
                                 ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$1_16 (select HEAP$1_old _$1_15)))
                                    (let
                                       ((.01$1_0 _$1_16)
                                        (sb$1_0 sb$1_0_old))
                                       (=>
                                          (and
                                             (let
                                                ((_$2_1 (distinct .01$2_0_old 0)))
                                                (=>
                                                   _$2_1
                                                   (let
                                                      ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                      (let
                                                         ((_$2_6 (select HEAP$2_old _$2_5))
                                                          (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                         (let
                                                            ((_$2_8 (select HEAP$2_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (= _$2_6 _$2_8)))
                                                               (=>
                                                                  _$2_9
                                                                  (let
                                                                     ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                                     (let
                                                                        ((_$2_11 (select HEAP$2_old _$2_10))
                                                                         (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                                        (let
                                                                           ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                           (let
                                                                              ((_$2_14 (= _$2_11 _$2_13)))
                                                                              (=>
                                                                                 (not _$2_14)
                                                                                 (let
                                                                                    ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                                    (let
                                                                                       ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                                       (let
                                                                                          ((.01$2_0 _$2_16)
                                                                                           (sb$2_0 sb$2_0_old))
                                                                                          false)))))))))))))))
                                             (let
                                                ((_$2_1 (distinct .01$2_0_old 0)))
                                                (=>
                                                   _$2_1
                                                   (let
                                                      ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                      (let
                                                         ((_$2_6 (select HEAP$2_old _$2_5))
                                                          (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                         (let
                                                            ((_$2_8 (select HEAP$2_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (= _$2_6 _$2_8)))
                                                               (=>
                                                                  (not _$2_9)
                                                                  (let
                                                                     ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                     (let
                                                                        ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                        (let
                                                                           ((.01$2_0 _$2_16)
                                                                            (sb$2_0 sb$2_0_old))
                                                                           false)))))))))))
                                          (INV_42_MAIN .01$1_0 sb$1_0 .01$2_0_old sb$2_0_old)))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$2_1 (distinct .01$2_0_old 0)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$2_6 (select HEAP$2_old _$2_5))
                      (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$2_8 (select HEAP$2_old _$2_7)))
                        (let
                           ((_$2_9 (= _$2_6 _$2_8)))
                           (=>
                              _$2_9
                              (let
                                 ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$2_11 (select HEAP$2_old _$2_10))
                                     (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$2_13 (select HEAP$2_old _$2_12)))
                                       (let
                                          ((_$2_14 (= _$2_11 _$2_13)))
                                          (=>
                                             (not _$2_14)
                                             (let
                                                ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$2_16 (select HEAP$2_old _$2_15)))
                                                   (let
                                                      ((.01$2_0 _$2_16)
                                                       (sb$2_0 sb$2_0_old))
                                                      (=>
                                                         (and
                                                            (let
                                                               ((_$1_1 (distinct .01$1_0_old 0)))
                                                               (=>
                                                                  _$1_1
                                                                  (let
                                                                     ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                                                                     (let
                                                                        ((_$1_6 (select HEAP$1_old _$1_5))
                                                                         (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                                                                        (let
                                                                           ((_$1_8 (select HEAP$1_old _$1_7)))
                                                                           (let
                                                                              ((_$1_9 (= _$1_6 _$1_8)))
                                                                              (=>
                                                                                 _$1_9
                                                                                 (let
                                                                                    ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                                                                    (let
                                                                                       ((_$1_11 (select HEAP$1_old _$1_10))
                                                                                        (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                                                                       (let
                                                                                          ((_$1_13 (select HEAP$1_old _$1_12)))
                                                                                          (let
                                                                                             ((_$1_14 (= _$1_11 _$1_13)))
                                                                                             (=>
                                                                                                (not _$1_14)
                                                                                                (let
                                                                                                   ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                                                                   (let
                                                                                                      ((_$1_16 (select HEAP$1_old _$1_15)))
                                                                                                      (let
                                                                                                         ((.01$1_0 _$1_16)
                                                                                                          (sb$1_0 sb$1_0_old))
                                                                                                         false)))))))))))))))
                                                            (let
                                                               ((_$1_1 (distinct .01$1_0_old 0)))
                                                               (=>
                                                                  _$1_1
                                                                  (let
                                                                     ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                                                                     (let
                                                                        ((_$1_6 (select HEAP$1_old _$1_5))
                                                                         (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                                                                        (let
                                                                           ((_$1_8 (select HEAP$1_old _$1_7)))
                                                                           (let
                                                                              ((_$1_9 (= _$1_6 _$1_8)))
                                                                              (=>
                                                                                 (not _$1_9)
                                                                                 (let
                                                                                    ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                                                    (let
                                                                                       ((_$1_16 (select HEAP$1_old _$1_15)))
                                                                                       (let
                                                                                          ((.01$1_0 _$1_16)
                                                                                           (sb$1_0 sb$1_0_old))
                                                                                          false)))))))))))
                                                         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0 sb$2_0))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$2_1 (distinct .01$2_0_old 0)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$2_6 (select HEAP$2_old _$2_5))
                      (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$2_8 (select HEAP$2_old _$2_7)))
                        (let
                           ((_$2_9 (= _$2_6 _$2_8)))
                           (=>
                              (not _$2_9)
                              (let
                                 ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$2_16 (select HEAP$2_old _$2_15)))
                                    (let
                                       ((.01$2_0 _$2_16)
                                        (sb$2_0 sb$2_0_old))
                                       (=>
                                          (and
                                             (let
                                                ((_$1_1 (distinct .01$1_0_old 0)))
                                                (=>
                                                   _$1_1
                                                   (let
                                                      ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                                                      (let
                                                         ((_$1_6 (select HEAP$1_old _$1_5))
                                                          (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                                                         (let
                                                            ((_$1_8 (select HEAP$1_old _$1_7)))
                                                            (let
                                                               ((_$1_9 (= _$1_6 _$1_8)))
                                                               (=>
                                                                  _$1_9
                                                                  (let
                                                                     ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                                                     (let
                                                                        ((_$1_11 (select HEAP$1_old _$1_10))
                                                                         (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                                                        (let
                                                                           ((_$1_13 (select HEAP$1_old _$1_12)))
                                                                           (let
                                                                              ((_$1_14 (= _$1_11 _$1_13)))
                                                                              (=>
                                                                                 (not _$1_14)
                                                                                 (let
                                                                                    ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                                                    (let
                                                                                       ((_$1_16 (select HEAP$1_old _$1_15)))
                                                                                       (let
                                                                                          ((.01$1_0 _$1_16)
                                                                                           (sb$1_0 sb$1_0_old))
                                                                                          false)))))))))))))))
                                             (let
                                                ((_$1_1 (distinct .01$1_0_old 0)))
                                                (=>
                                                   _$1_1
                                                   (let
                                                      ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                                                      (let
                                                         ((_$1_6 (select HEAP$1_old _$1_5))
                                                          (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                                                         (let
                                                            ((_$1_8 (select HEAP$1_old _$1_7)))
                                                            (let
                                                               ((_$1_9 (= _$1_6 _$1_8)))
                                                               (=>
                                                                  (not _$1_9)
                                                                  (let
                                                                     ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                                     (let
                                                                        ((_$1_16 (select HEAP$1_old _$1_15)))
                                                                        (let
                                                                           ((.01$1_0 _$1_16)
                                                                            (sb$1_0 sb$1_0_old))
                                                                           false)))))))))))
                                          (INV_42_MAIN .01$1_0_old sb$1_0_old .01$2_0 sb$2_0)))))))))))))))
; end
(assert
   (forall
      ((sb$1_0_old Int)
       (ancestors$1_0_old Int)
       (sb$2_0_old Int)
       (ancestors$2_0_old Int))
      (=>
         (INV_REC_is_ancestor_PRE sb$1_0_old ancestors$1_0_old sb$2_0_old ancestors$2_0_old)
         (let
            ((.01$1_0 ancestors$1_0_old)
             (sb$1_0 sb$1_0_old)
             (.01$2_0 ancestors$2_0_old)
             (sb$2_0 sb$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_42_PRE .01$1_0 sb$1_0 .01$2_0 sb$2_0)
                  (=>
                     (INV_42 .01$1_0 sb$1_0 .01$2_0 sb$2_0 result$1 result$2)
                     (INV_REC_is_ancestor sb$1_0_old ancestors$1_0_old sb$2_0_old ancestors$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             _$1_14
                                             (let
                                                ((.0$1_0 true))
                                                (let
                                                   ((result$1 .0$1_0)
                                                    (_$2_1 (distinct .01$2_0_old 0)))
                                                   (=>
                                                      _$2_1
                                                      (let
                                                         ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                         (let
                                                            ((_$2_6 (select HEAP$2_old _$2_5))
                                                             (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                            (let
                                                               ((_$2_8 (select HEAP$2_old _$2_7)))
                                                               (let
                                                                  ((_$2_9 (= _$2_6 _$2_8)))
                                                                  (=>
                                                                     _$2_9
                                                                     (let
                                                                        ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                                        (let
                                                                           ((_$2_11 (select HEAP$2_old _$2_10))
                                                                            (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                                           (let
                                                                              ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                              (let
                                                                                 ((_$2_14 (= _$2_11 _$2_13)))
                                                                                 (=>
                                                                                    _$2_14
                                                                                    (let
                                                                                       ((.0$2_0 true))
                                                                                       (let
                                                                                          ((result$2 .0$2_0))
                                                                                          (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             _$1_14
                                             (let
                                                ((.0$1_0 true))
                                                (let
                                                   ((result$1 .0$1_0)
                                                    (_$2_1 (distinct .01$2_0_old 0)))
                                                   (=>
                                                      (not _$2_1)
                                                      (let
                                                         ((.0$2_0 false))
                                                         (let
                                                            ((result$2 .0$2_0))
                                                            (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               (not _$1_1)
               (let
                  ((.0$1_0 false))
                  (let
                     ((result$1 .0$1_0)
                      (_$2_1 (distinct .01$2_0_old 0)))
                     (=>
                        _$2_1
                        (let
                           ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                           (let
                              ((_$2_6 (select HEAP$2_old _$2_5))
                               (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                              (let
                                 ((_$2_8 (select HEAP$2_old _$2_7)))
                                 (let
                                    ((_$2_9 (= _$2_6 _$2_8)))
                                    (=>
                                       _$2_9
                                       (let
                                          ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                          (let
                                             ((_$2_11 (select HEAP$2_old _$2_10))
                                              (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                             (let
                                                ((_$2_13 (select HEAP$2_old _$2_12)))
                                                (let
                                                   ((_$2_14 (= _$2_11 _$2_13)))
                                                   (=>
                                                      _$2_14
                                                      (let
                                                         ((.0$2_0 true))
                                                         (let
                                                            ((result$2 .0$2_0))
                                                            (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               (not _$1_1)
               (let
                  ((.0$1_0 false))
                  (let
                     ((result$1 .0$1_0)
                      (_$2_1 (distinct .01$2_0_old 0)))
                     (=>
                        (not _$2_1)
                        (let
                           ((.0$2_0 false))
                           (let
                              ((result$2 .0$2_0))
                              (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             (not _$1_14)
                                             (let
                                                ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$1_16 (select HEAP$1_old _$1_15)))
                                                   (let
                                                      ((.01$1_0 _$1_16)
                                                       (sb$1_0 sb$1_0_old)
                                                       (_$2_1 (distinct .01$2_0_old 0)))
                                                      (=>
                                                         _$2_1
                                                         (let
                                                            ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                            (let
                                                               ((_$2_6 (select HEAP$2_old _$2_5))
                                                                (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                               (let
                                                                  ((_$2_8 (select HEAP$2_old _$2_7)))
                                                                  (let
                                                                     ((_$2_9 (= _$2_6 _$2_8)))
                                                                     (=>
                                                                        _$2_9
                                                                        (let
                                                                           ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                                           (let
                                                                              ((_$2_11 (select HEAP$2_old _$2_10))
                                                                               (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                                              (let
                                                                                 ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                                 (let
                                                                                    ((_$2_14 (= _$2_11 _$2_13)))
                                                                                    (=>
                                                                                       (not _$2_14)
                                                                                       (let
                                                                                          ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                                          (let
                                                                                             ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                                             (let
                                                                                                ((.01$2_0 _$2_16)
                                                                                                 (sb$2_0 sb$2_0_old))
                                                                                                (forall
                                                                                                   ((result$1 Int)
                                                                                                    (result$2 Int))
                                                                                                   (and
                                                                                                      (INV_42_PRE .01$1_0 sb$1_0 .01$2_0 sb$2_0)
                                                                                                      (=>
                                                                                                         (INV_42 .01$1_0 sb$1_0 .01$2_0 sb$2_0 result$1 result$2)
                                                                                                         (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2))))))))))))))))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             (not _$1_14)
                                             (let
                                                ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$1_16 (select HEAP$1_old _$1_15)))
                                                   (let
                                                      ((.01$1_0 _$1_16)
                                                       (sb$1_0 sb$1_0_old)
                                                       (_$2_1 (distinct .01$2_0_old 0)))
                                                      (=>
                                                         _$2_1
                                                         (let
                                                            ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                            (let
                                                               ((_$2_6 (select HEAP$2_old _$2_5))
                                                                (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                               (let
                                                                  ((_$2_8 (select HEAP$2_old _$2_7)))
                                                                  (let
                                                                     ((_$2_9 (= _$2_6 _$2_8)))
                                                                     (=>
                                                                        (not _$2_9)
                                                                        (let
                                                                           ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                           (let
                                                                              ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                              (let
                                                                                 ((.01$2_0 _$2_16)
                                                                                  (sb$2_0 sb$2_0_old))
                                                                                 (forall
                                                                                    ((result$1 Int)
                                                                                     (result$2 Int))
                                                                                    (and
                                                                                       (INV_42_PRE .01$1_0 sb$1_0 .01$2_0 sb$2_0)
                                                                                       (=>
                                                                                          (INV_42 .01$1_0 sb$1_0 .01$2_0 sb$2_0 result$1 result$2)
                                                                                          (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              (not _$1_9)
                              (let
                                 ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$1_16 (select HEAP$1_old _$1_15)))
                                    (let
                                       ((.01$1_0 _$1_16)
                                        (sb$1_0 sb$1_0_old)
                                        (_$2_1 (distinct .01$2_0_old 0)))
                                       (=>
                                          _$2_1
                                          (let
                                             ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                             (let
                                                ((_$2_6 (select HEAP$2_old _$2_5))
                                                 (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                (let
                                                   ((_$2_8 (select HEAP$2_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (= _$2_6 _$2_8)))
                                                      (=>
                                                         _$2_9
                                                         (let
                                                            ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                            (let
                                                               ((_$2_11 (select HEAP$2_old _$2_10))
                                                                (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                               (let
                                                                  ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                  (let
                                                                     ((_$2_14 (= _$2_11 _$2_13)))
                                                                     (=>
                                                                        (not _$2_14)
                                                                        (let
                                                                           ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                           (let
                                                                              ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                              (let
                                                                                 ((.01$2_0 _$2_16)
                                                                                  (sb$2_0 sb$2_0_old))
                                                                                 (forall
                                                                                    ((result$1 Int)
                                                                                     (result$2 Int))
                                                                                    (and
                                                                                       (INV_42_PRE .01$1_0 sb$1_0 .01$2_0 sb$2_0)
                                                                                       (=>
                                                                                          (INV_42 .01$1_0 sb$1_0 .01$2_0 sb$2_0 result$1 result$2)
                                                                                          (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2)))))))))))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              (not _$1_9)
                              (let
                                 ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$1_16 (select HEAP$1_old _$1_15)))
                                    (let
                                       ((.01$1_0 _$1_16)
                                        (sb$1_0 sb$1_0_old)
                                        (_$2_1 (distinct .01$2_0_old 0)))
                                       (=>
                                          _$2_1
                                          (let
                                             ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                             (let
                                                ((_$2_6 (select HEAP$2_old _$2_5))
                                                 (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                (let
                                                   ((_$2_8 (select HEAP$2_old _$2_7)))
                                                   (let
                                                      ((_$2_9 (= _$2_6 _$2_8)))
                                                      (=>
                                                         (not _$2_9)
                                                         (let
                                                            ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                            (let
                                                               ((_$2_16 (select HEAP$2_old _$2_15)))
                                                               (let
                                                                  ((.01$2_0 _$2_16)
                                                                   (sb$2_0 sb$2_0_old))
                                                                  (forall
                                                                     ((result$1 Int)
                                                                      (result$2 Int))
                                                                     (and
                                                                        (INV_42_PRE .01$1_0 sb$1_0 .01$2_0 sb$2_0)
                                                                        (=>
                                                                           (INV_42 .01$1_0 sb$1_0 .01$2_0 sb$2_0 result$1 result$2)
                                                                           (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2))))))))))))))))))))))))))
(assert
   (forall
      ((sb$1_0_old Int)
       (ancestors$1_0_old Int))
      (=>
         (INV_REC_is_ancestor__1_PRE sb$1_0_old ancestors$1_0_old)
         (let
            ((.01$1_0 ancestors$1_0_old)
             (sb$1_0 sb$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_42__1 .01$1_0 sb$1_0 result$1)
                  (INV_REC_is_ancestor__1 sb$1_0_old ancestors$1_0_old result$1)))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int))
      (=>
         (INV_42__1_PRE .01$1_0_old sb$1_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             _$1_14
                                             (let
                                                ((.0$1_0 true))
                                                (let
                                                   ((result$1 .0$1_0))
                                                   (INV_42__1 .01$1_0_old sb$1_0_old result$1))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int))
      (=>
         (INV_42__1_PRE .01$1_0_old sb$1_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               (not _$1_1)
               (let
                  ((.0$1_0 false))
                  (let
                     ((result$1 .0$1_0))
                     (INV_42__1 .01$1_0_old sb$1_0_old result$1))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int))
      (=>
         (INV_42__1_PRE .01$1_0_old sb$1_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             (not _$1_14)
                                             (let
                                                ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$1_16 (select HEAP$1_old _$1_15)))
                                                   (let
                                                      ((.01$1_0 _$1_16)
                                                       (sb$1_0 sb$1_0_old))
                                                      (forall
                                                         ((result$1 Int))
                                                         (=>
                                                            (INV_42__1 .01$1_0 sb$1_0 result$1)
                                                            (INV_42__1 .01$1_0_old sb$1_0_old result$1)))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int))
      (=>
         (INV_42__1_PRE .01$1_0_old sb$1_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              (not _$1_9)
                              (let
                                 ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$1_16 (select HEAP$1_old _$1_15)))
                                    (let
                                       ((.01$1_0 _$1_16)
                                        (sb$1_0 sb$1_0_old))
                                       (forall
                                          ((result$1 Int))
                                          (=>
                                             (INV_42__1 .01$1_0 sb$1_0 result$1)
                                             (INV_42__1 .01$1_0_old sb$1_0_old result$1))))))))))))))))
(assert
   (forall
      ((sb$2_0_old Int)
       (ancestors$2_0_old Int))
      (=>
         (INV_REC_is_ancestor__2_PRE sb$2_0_old ancestors$2_0_old)
         (let
            ((.01$2_0 ancestors$2_0_old)
             (sb$2_0 sb$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_42__2 .01$2_0 sb$2_0 result$2)
                  (INV_REC_is_ancestor__2 sb$2_0_old ancestors$2_0_old result$2)))))))
(assert
   (forall
      ((.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42__2_PRE .01$2_0_old sb$2_0_old)
         (let
            ((_$2_1 (distinct .01$2_0_old 0)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$2_6 (select HEAP$2_old _$2_5))
                      (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$2_8 (select HEAP$2_old _$2_7)))
                        (let
                           ((_$2_9 (= _$2_6 _$2_8)))
                           (=>
                              _$2_9
                              (let
                                 ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$2_11 (select HEAP$2_old _$2_10))
                                     (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$2_13 (select HEAP$2_old _$2_12)))
                                       (let
                                          ((_$2_14 (= _$2_11 _$2_13)))
                                          (=>
                                             _$2_14
                                             (let
                                                ((.0$2_0 true))
                                                (let
                                                   ((result$2 .0$2_0))
                                                   (INV_42__2 .01$2_0_old sb$2_0_old result$2))))))))))))))))))
(assert
   (forall
      ((.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42__2_PRE .01$2_0_old sb$2_0_old)
         (let
            ((_$2_1 (distinct .01$2_0_old 0)))
            (=>
               (not _$2_1)
               (let
                  ((.0$2_0 false))
                  (let
                     ((result$2 .0$2_0))
                     (INV_42__2 .01$2_0_old sb$2_0_old result$2))))))))
(assert
   (forall
      ((.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42__2_PRE .01$2_0_old sb$2_0_old)
         (let
            ((_$2_1 (distinct .01$2_0_old 0)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$2_6 (select HEAP$2_old _$2_5))
                      (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$2_8 (select HEAP$2_old _$2_7)))
                        (let
                           ((_$2_9 (= _$2_6 _$2_8)))
                           (=>
                              _$2_9
                              (let
                                 ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$2_11 (select HEAP$2_old _$2_10))
                                     (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$2_13 (select HEAP$2_old _$2_12)))
                                       (let
                                          ((_$2_14 (= _$2_11 _$2_13)))
                                          (=>
                                             (not _$2_14)
                                             (let
                                                ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$2_16 (select HEAP$2_old _$2_15)))
                                                   (let
                                                      ((.01$2_0 _$2_16)
                                                       (sb$2_0 sb$2_0_old))
                                                      (forall
                                                         ((result$2 Int))
                                                         (=>
                                                            (INV_42__2 .01$2_0 sb$2_0 result$2)
                                                            (INV_42__2 .01$2_0_old sb$2_0_old result$2)))))))))))))))))))))
(assert
   (forall
      ((.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42__2_PRE .01$2_0_old sb$2_0_old)
         (let
            ((_$2_1 (distinct .01$2_0_old 0)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$2_6 (select HEAP$2_old _$2_5))
                      (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$2_8 (select HEAP$2_old _$2_7)))
                        (let
                           ((_$2_9 (= _$2_6 _$2_8)))
                           (=>
                              (not _$2_9)
                              (let
                                 ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$2_16 (select HEAP$2_old _$2_15)))
                                    (let
                                       ((.01$2_0 _$2_16)
                                        (sb$2_0 sb$2_0_old))
                                       (forall
                                          ((result$2 Int))
                                          (=>
                                             (INV_42__2 .01$2_0 sb$2_0 result$2)
                                             (INV_42__2 .01$2_0_old sb$2_0_old result$2))))))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              _$1_9
                              (let
                                 ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$1_11 (select HEAP$1_old _$1_10))
                                     (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$1_13 (select HEAP$1_old _$1_12)))
                                       (let
                                          ((_$1_14 (= _$1_11 _$1_13)))
                                          (=>
                                             (not _$1_14)
                                             (let
                                                ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$1_16 (select HEAP$1_old _$1_15)))
                                                   (let
                                                      ((.01$1_0 _$1_16)
                                                       (sb$1_0 sb$1_0_old))
                                                      (=>
                                                         (and
                                                            (let
                                                               ((_$2_1 (distinct .01$2_0_old 0)))
                                                               (=>
                                                                  _$2_1
                                                                  (let
                                                                     ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                                     (let
                                                                        ((_$2_6 (select HEAP$2_old _$2_5))
                                                                         (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                                        (let
                                                                           ((_$2_8 (select HEAP$2_old _$2_7)))
                                                                           (let
                                                                              ((_$2_9 (= _$2_6 _$2_8)))
                                                                              (=>
                                                                                 _$2_9
                                                                                 (let
                                                                                    ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                                                    (let
                                                                                       ((_$2_11 (select HEAP$2_old _$2_10))
                                                                                        (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                                                       (let
                                                                                          ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                                          (let
                                                                                             ((_$2_14 (= _$2_11 _$2_13)))
                                                                                             (=>
                                                                                                (not _$2_14)
                                                                                                (let
                                                                                                   ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                                                   (let
                                                                                                      ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                                                      (let
                                                                                                         ((.01$2_0 _$2_16)
                                                                                                          (sb$2_0 sb$2_0_old))
                                                                                                         false)))))))))))))))
                                                            (let
                                                               ((_$2_1 (distinct .01$2_0_old 0)))
                                                               (=>
                                                                  _$2_1
                                                                  (let
                                                                     ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                                     (let
                                                                        ((_$2_6 (select HEAP$2_old _$2_5))
                                                                         (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                                        (let
                                                                           ((_$2_8 (select HEAP$2_old _$2_7)))
                                                                           (let
                                                                              ((_$2_9 (= _$2_6 _$2_8)))
                                                                              (=>
                                                                                 (not _$2_9)
                                                                                 (let
                                                                                    ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                                    (let
                                                                                       ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                                       (let
                                                                                          ((.01$2_0 _$2_16)
                                                                                           (sb$2_0 sb$2_0_old))
                                                                                          false)))))))))))
                                                         (forall
                                                            ((result$1 Int)
                                                             (result$2 Int))
                                                            (and
                                                               (INV_42_PRE .01$1_0 sb$1_0 .01$2_0_old sb$2_0_old)
                                                               (=>
                                                                  (INV_42 .01$1_0 sb$1_0 .01$2_0_old sb$2_0_old result$1 result$2)
                                                                  (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2)))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$1_1 (distinct .01$1_0_old 0)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$1_6 (select HEAP$1_old _$1_5))
                      (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$1_8 (select HEAP$1_old _$1_7)))
                        (let
                           ((_$1_9 (= _$1_6 _$1_8)))
                           (=>
                              (not _$1_9)
                              (let
                                 ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$1_16 (select HEAP$1_old _$1_15)))
                                    (let
                                       ((.01$1_0 _$1_16)
                                        (sb$1_0 sb$1_0_old))
                                       (=>
                                          (and
                                             (let
                                                ((_$2_1 (distinct .01$2_0_old 0)))
                                                (=>
                                                   _$2_1
                                                   (let
                                                      ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                      (let
                                                         ((_$2_6 (select HEAP$2_old _$2_5))
                                                          (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                         (let
                                                            ((_$2_8 (select HEAP$2_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (= _$2_6 _$2_8)))
                                                               (=>
                                                                  _$2_9
                                                                  (let
                                                                     ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                                                     (let
                                                                        ((_$2_11 (select HEAP$2_old _$2_10))
                                                                         (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                                                        (let
                                                                           ((_$2_13 (select HEAP$2_old _$2_12)))
                                                                           (let
                                                                              ((_$2_14 (= _$2_11 _$2_13)))
                                                                              (=>
                                                                                 (not _$2_14)
                                                                                 (let
                                                                                    ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                                    (let
                                                                                       ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                                       (let
                                                                                          ((.01$2_0 _$2_16)
                                                                                           (sb$2_0 sb$2_0_old))
                                                                                          false)))))))))))))))
                                             (let
                                                ((_$2_1 (distinct .01$2_0_old 0)))
                                                (=>
                                                   _$2_1
                                                   (let
                                                      ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                                                      (let
                                                         ((_$2_6 (select HEAP$2_old _$2_5))
                                                          (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                                                         (let
                                                            ((_$2_8 (select HEAP$2_old _$2_7)))
                                                            (let
                                                               ((_$2_9 (= _$2_6 _$2_8)))
                                                               (=>
                                                                  (not _$2_9)
                                                                  (let
                                                                     ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                                     (let
                                                                        ((_$2_16 (select HEAP$2_old _$2_15)))
                                                                        (let
                                                                           ((.01$2_0 _$2_16)
                                                                            (sb$2_0 sb$2_0_old))
                                                                           false)))))))))))
                                          (forall
                                             ((result$1 Int)
                                              (result$2 Int))
                                             (and
                                                (INV_42_PRE .01$1_0 sb$1_0 .01$2_0_old sb$2_0_old)
                                                (=>
                                                   (INV_42 .01$1_0 sb$1_0 .01$2_0_old sb$2_0_old result$1 result$2)
                                                   (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$2_1 (distinct .01$2_0_old 0)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$2_6 (select HEAP$2_old _$2_5))
                      (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$2_8 (select HEAP$2_old _$2_7)))
                        (let
                           ((_$2_9 (= _$2_6 _$2_8)))
                           (=>
                              _$2_9
                              (let
                                 ((_$2_10 (+ .01$2_0_old (+ (* 3 0) 2))))
                                 (let
                                    ((_$2_11 (select HEAP$2_old _$2_10))
                                     (_$2_12 (+ sb$2_0_old (+ (* 18 0) 0))))
                                    (let
                                       ((_$2_13 (select HEAP$2_old _$2_12)))
                                       (let
                                          ((_$2_14 (= _$2_11 _$2_13)))
                                          (=>
                                             (not _$2_14)
                                             (let
                                                ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                                (let
                                                   ((_$2_16 (select HEAP$2_old _$2_15)))
                                                   (let
                                                      ((.01$2_0 _$2_16)
                                                       (sb$2_0 sb$2_0_old))
                                                      (=>
                                                         (and
                                                            (let
                                                               ((_$1_1 (distinct .01$1_0_old 0)))
                                                               (=>
                                                                  _$1_1
                                                                  (let
                                                                     ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                                                                     (let
                                                                        ((_$1_6 (select HEAP$1_old _$1_5))
                                                                         (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                                                                        (let
                                                                           ((_$1_8 (select HEAP$1_old _$1_7)))
                                                                           (let
                                                                              ((_$1_9 (= _$1_6 _$1_8)))
                                                                              (=>
                                                                                 _$1_9
                                                                                 (let
                                                                                    ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                                                                    (let
                                                                                       ((_$1_11 (select HEAP$1_old _$1_10))
                                                                                        (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                                                                       (let
                                                                                          ((_$1_13 (select HEAP$1_old _$1_12)))
                                                                                          (let
                                                                                             ((_$1_14 (= _$1_11 _$1_13)))
                                                                                             (=>
                                                                                                (not _$1_14)
                                                                                                (let
                                                                                                   ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                                                                   (let
                                                                                                      ((_$1_16 (select HEAP$1_old _$1_15)))
                                                                                                      (let
                                                                                                         ((.01$1_0 _$1_16)
                                                                                                          (sb$1_0 sb$1_0_old))
                                                                                                         false)))))))))))))))
                                                            (let
                                                               ((_$1_1 (distinct .01$1_0_old 0)))
                                                               (=>
                                                                  _$1_1
                                                                  (let
                                                                     ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                                                                     (let
                                                                        ((_$1_6 (select HEAP$1_old _$1_5))
                                                                         (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                                                                        (let
                                                                           ((_$1_8 (select HEAP$1_old _$1_7)))
                                                                           (let
                                                                              ((_$1_9 (= _$1_6 _$1_8)))
                                                                              (=>
                                                                                 (not _$1_9)
                                                                                 (let
                                                                                    ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                                                    (let
                                                                                       ((_$1_16 (select HEAP$1_old _$1_15)))
                                                                                       (let
                                                                                          ((.01$1_0 _$1_16)
                                                                                           (sb$1_0 sb$1_0_old))
                                                                                          false)))))))))))
                                                         (forall
                                                            ((result$1 Int)
                                                             (result$2 Int))
                                                            (and
                                                               (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0 sb$2_0)
                                                               (=>
                                                                  (INV_42 .01$1_0_old sb$1_0_old .01$2_0 sb$2_0 result$1 result$2)
                                                                  (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2)))))))))))))))))))))))
(assert
   (forall
      ((.01$1_0_old Int)
       (sb$1_0_old Int)
       (.01$2_0_old Int)
       (sb$2_0_old Int))
      (=>
         (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old)
         (let
            ((_$2_1 (distinct .01$2_0_old 0)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ .01$2_0_old (+ (* 3 0) 1))))
                  (let
                     ((_$2_6 (select HEAP$2_old _$2_5))
                      (_$2_7 (+ sb$2_0_old (+ (* 18 0) 1))))
                     (let
                        ((_$2_8 (select HEAP$2_old _$2_7)))
                        (let
                           ((_$2_9 (= _$2_6 _$2_8)))
                           (=>
                              (not _$2_9)
                              (let
                                 ((_$2_15 (+ .01$2_0_old (+ (* 3 0) 0))))
                                 (let
                                    ((_$2_16 (select HEAP$2_old _$2_15)))
                                    (let
                                       ((.01$2_0 _$2_16)
                                        (sb$2_0 sb$2_0_old))
                                       (=>
                                          (and
                                             (let
                                                ((_$1_1 (distinct .01$1_0_old 0)))
                                                (=>
                                                   _$1_1
                                                   (let
                                                      ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                                                      (let
                                                         ((_$1_6 (select HEAP$1_old _$1_5))
                                                          (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                                                         (let
                                                            ((_$1_8 (select HEAP$1_old _$1_7)))
                                                            (let
                                                               ((_$1_9 (= _$1_6 _$1_8)))
                                                               (=>
                                                                  _$1_9
                                                                  (let
                                                                     ((_$1_10 (+ .01$1_0_old (+ (* 3 0) 2))))
                                                                     (let
                                                                        ((_$1_11 (select HEAP$1_old _$1_10))
                                                                         (_$1_12 (+ sb$1_0_old (+ (* 18 0) 0))))
                                                                        (let
                                                                           ((_$1_13 (select HEAP$1_old _$1_12)))
                                                                           (let
                                                                              ((_$1_14 (= _$1_11 _$1_13)))
                                                                              (=>
                                                                                 (not _$1_14)
                                                                                 (let
                                                                                    ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                                                    (let
                                                                                       ((_$1_16 (select HEAP$1_old _$1_15)))
                                                                                       (let
                                                                                          ((.01$1_0 _$1_16)
                                                                                           (sb$1_0 sb$1_0_old))
                                                                                          false)))))))))))))))
                                             (let
                                                ((_$1_1 (distinct .01$1_0_old 0)))
                                                (=>
                                                   _$1_1
                                                   (let
                                                      ((_$1_5 (+ .01$1_0_old (+ (* 3 0) 1))))
                                                      (let
                                                         ((_$1_6 (select HEAP$1_old _$1_5))
                                                          (_$1_7 (+ sb$1_0_old (+ (* 18 0) 1))))
                                                         (let
                                                            ((_$1_8 (select HEAP$1_old _$1_7)))
                                                            (let
                                                               ((_$1_9 (= _$1_6 _$1_8)))
                                                               (=>
                                                                  (not _$1_9)
                                                                  (let
                                                                     ((_$1_15 (+ .01$1_0_old (+ (* 3 0) 0))))
                                                                     (let
                                                                        ((_$1_16 (select HEAP$1_old _$1_15)))
                                                                        (let
                                                                           ((.01$1_0 _$1_16)
                                                                            (sb$1_0 sb$1_0_old))
                                                                           false)))))))))))
                                          (forall
                                             ((result$1 Int)
                                              (result$2 Int))
                                             (and
                                                (INV_42_PRE .01$1_0_old sb$1_0_old .01$2_0 sb$2_0)
                                                (=>
                                                   (INV_42 .01$1_0_old sb$1_0_old .01$2_0 sb$2_0 result$1 result$2)
                                                   (INV_42 .01$1_0_old sb$1_0_old .01$2_0_old sb$2_0_old result$1 result$2))))))))))))))))))
(check-sat)
(get-model)
