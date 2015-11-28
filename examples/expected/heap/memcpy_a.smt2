(set-logic HORN)
(define-fun
   IN_INV
   ((dest$1_0 Int)
    (src$1_0 Int)
    (size$1_0 Int)
    (dest$2_0 Int)
    (src$2_0 Int)
    (size$2_0 Int))
   Bool
   (and
      (= dest$1_0 dest$2_0)
      (= src$1_0 src$2_0)
      (= size$1_0 size$2_0)))
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
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_memcpy
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
   INV_REC_memcpy_PRE
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_memcpy__1
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_memcpy__1_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_memcpy__2
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_memcpy__2_PRE
   (Int
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
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1
   (Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1_PRE
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
      ((dest$1_0_old Int)
       (src$1_0_old Int)
       (size$1_0_old Int)
       (dest$2_0_old Int)
       (src$2_0_old Int)
       (size$2_0_old Int))
      (=>
         (IN_INV
            dest$1_0_old
            src$1_0_old
            size$1_0_old
            dest$2_0_old
            src$2_0_old
            size$2_0_old)
         (let
            ((i.0$1_0 0)
             (dest$1_0 dest$1_0_old)
             (size$1_0 size$1_0_old)
             (src$1_0 src$1_0_old)
             (.01$2_0 src$2_0_old)
             (.0$2_0 dest$2_0_old)
             (size$2_0 size$2_0_old)
             (src$2_0 src$2_0_old))
            (INV_42_MAIN dest$1_0 i.0$1_0 size$1_0 src$1_0 .0$2_0 .01$2_0 size$2_0 src$2_0)))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42_MAIN dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old size$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 1)
                   (_$2_1 .01$2_0_old)
                   (_$2_2 src$2_0_old))
                  (let
                     ((_$2_3 (- _$2_1 _$2_2)))
                     (let
                        ((_$2_4 _$2_3)
                         (_$2_5 size$2_0_old))
                        (let
                           ((_$2_6 (< _$2_4 _$2_5)))
                           (=>
                              (not _$2_6)
                              (let
                                 ((result$2 1))
                                 (OUT_INV
                                    result$1
                                    result$2))))))))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42_MAIN dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old size$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ src$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ dest$1_0_old _$1_8)))
                           (let
                              ((HEAP$1 (store HEAP$1_old _$1_9 _$1_7))
                               (_$1_10 (+ i.0$1_0_old 1)))
                              (let
                                 ((i.0$1_0 _$1_10)
                                  (dest$1_0 dest$1_0_old)
                                  (size$1_0 size$1_0_old)
                                  (src$1_0 src$1_0_old)
                                  (_$2_1 .01$2_0_old)
                                  (_$2_2 src$2_0_old))
                                 (let
                                    ((_$2_3 (- _$2_1 _$2_2)))
                                    (let
                                       ((_$2_4 _$2_3)
                                        (_$2_5 size$2_0_old))
                                       (let
                                          ((_$2_6 (< _$2_4 _$2_5)))
                                          (=>
                                             _$2_6
                                             (let
                                                ((_$2_10 (select HEAP$2_old .01$2_0_old)))
                                                (let
                                                   ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_10))
                                                    (_$2_11 (+ .0$2_0_old 1))
                                                    (_$2_12 (+ .01$2_0_old 1)))
                                                   (let
                                                      ((.01$2_0 _$2_12)
                                                       (.0$2_0 _$2_11)
                                                       (size$2_0 size$2_0_old)
                                                       (src$2_0 src$2_0_old))
                                                      (INV_42_MAIN dest$1_0 i.0$1_0 size$1_0 src$1_0 .0$2_0 .01$2_0 size$2_0 src$2_0)))))))))))))))))))
; forbidden main
; offbyn main
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42_MAIN dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old size$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ src$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ dest$1_0_old _$1_8)))
                           (let
                              ((HEAP$1 (store HEAP$1_old _$1_9 _$1_7))
                               (_$1_10 (+ i.0$1_0_old 1)))
                              (let
                                 ((i.0$1_0 _$1_10)
                                  (dest$1_0 dest$1_0_old)
                                  (size$1_0 size$1_0_old)
                                  (src$1_0 src$1_0_old))
                                 (=>
                                    (and
                                       (let
                                          ((_$2_1 .01$2_0_old)
                                           (_$2_2 src$2_0_old))
                                          (let
                                             ((_$2_3 (- _$2_1 _$2_2)))
                                             (let
                                                ((_$2_4 _$2_3)
                                                 (_$2_5 size$2_0_old))
                                                (let
                                                   ((_$2_6 (< _$2_4 _$2_5)))
                                                   (=>
                                                      _$2_6
                                                      (let
                                                         ((_$2_10 (select HEAP$2_old .01$2_0_old)))
                                                         (let
                                                            ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_10))
                                                             (_$2_11 (+ .0$2_0_old 1))
                                                             (_$2_12 (+ .01$2_0_old 1)))
                                                            (let
                                                               ((.01$2_0 _$2_12)
                                                                (.0$2_0 _$2_11)
                                                                (size$2_0 size$2_0_old)
                                                                (src$2_0 src$2_0_old))
                                                               false)))))))))
                                    (INV_42_MAIN dest$1_0 i.0$1_0 size$1_0 src$1_0 .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)))))))))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42_MAIN dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$2_1 .01$2_0_old)
             (_$2_2 src$2_0_old))
            (let
               ((_$2_3 (- _$2_1 _$2_2)))
               (let
                  ((_$2_4 _$2_3)
                   (_$2_5 size$2_0_old))
                  (let
                     ((_$2_6 (< _$2_4 _$2_5)))
                     (=>
                        _$2_6
                        (let
                           ((_$2_10 (select HEAP$2_old .01$2_0_old)))
                           (let
                              ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_10))
                               (_$2_11 (+ .0$2_0_old 1))
                               (_$2_12 (+ .01$2_0_old 1)))
                              (let
                                 ((.01$2_0 _$2_12)
                                  (.0$2_0 _$2_11)
                                  (size$2_0 size$2_0_old)
                                  (src$2_0 src$2_0_old))
                                 (=>
                                    (and
                                       (let
                                          ((_$1_1 (< i.0$1_0_old size$1_0_old)))
                                          (=>
                                             _$1_1
                                             (let
                                                ((_$1_5 i.0$1_0_old))
                                                (let
                                                   ((_$1_6 (+ src$1_0_old _$1_5)))
                                                   (let
                                                      ((_$1_7 (select HEAP$1_old _$1_6))
                                                       (_$1_8 i.0$1_0_old))
                                                      (let
                                                         ((_$1_9 (+ dest$1_0_old _$1_8)))
                                                         (let
                                                            ((HEAP$1 (store HEAP$1_old _$1_9 _$1_7))
                                                             (_$1_10 (+ i.0$1_0_old 1)))
                                                            (let
                                                               ((i.0$1_0 _$1_10)
                                                                (dest$1_0 dest$1_0_old)
                                                                (size$1_0 size$1_0_old)
                                                                (src$1_0 src$1_0_old))
                                                               false)))))))))
                                    (INV_42_MAIN dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0 .01$2_0 size$2_0 src$2_0)))))))))))))
; end
(assert
   (forall
      ((dest$1_0_old Int)
       (src$1_0_old Int)
       (size$1_0_old Int)
       (dest$2_0_old Int)
       (src$2_0_old Int)
       (size$2_0_old Int))
      (=>
         (INV_REC_memcpy_PRE dest$1_0_old src$1_0_old size$1_0_old dest$2_0_old src$2_0_old size$2_0_old)
         (let
            ((i.0$1_0 0)
             (dest$1_0 dest$1_0_old)
             (size$1_0 size$1_0_old)
             (src$1_0 src$1_0_old)
             (.01$2_0 src$2_0_old)
             (.0$2_0 dest$2_0_old)
             (size$2_0 size$2_0_old)
             (src$2_0 src$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_42_PRE dest$1_0 i.0$1_0 size$1_0 src$1_0 .0$2_0 .01$2_0 size$2_0 src$2_0)
                  (=>
                     (INV_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 .0$2_0 .01$2_0 size$2_0 src$2_0 result$1 result$2)
                     (INV_REC_memcpy dest$1_0_old src$1_0_old size$1_0_old dest$2_0_old src$2_0_old size$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42_PRE dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old size$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 1)
                   (_$2_1 .01$2_0_old)
                   (_$2_2 src$2_0_old))
                  (let
                     ((_$2_3 (- _$2_1 _$2_2)))
                     (let
                        ((_$2_4 _$2_3)
                         (_$2_5 size$2_0_old))
                        (let
                           ((_$2_6 (< _$2_4 _$2_5)))
                           (=>
                              (not _$2_6)
                              (let
                                 ((result$2 1))
                                 (INV_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42_PRE dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old size$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ src$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ dest$1_0_old _$1_8)))
                           (let
                              ((HEAP$1 (store HEAP$1_old _$1_9 _$1_7))
                               (_$1_10 (+ i.0$1_0_old 1)))
                              (let
                                 ((i.0$1_0 _$1_10)
                                  (dest$1_0 dest$1_0_old)
                                  (size$1_0 size$1_0_old)
                                  (src$1_0 src$1_0_old)
                                  (_$2_1 .01$2_0_old)
                                  (_$2_2 src$2_0_old))
                                 (let
                                    ((_$2_3 (- _$2_1 _$2_2)))
                                    (let
                                       ((_$2_4 _$2_3)
                                        (_$2_5 size$2_0_old))
                                       (let
                                          ((_$2_6 (< _$2_4 _$2_5)))
                                          (=>
                                             _$2_6
                                             (let
                                                ((_$2_10 (select HEAP$2_old .01$2_0_old)))
                                                (let
                                                   ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_10))
                                                    (_$2_11 (+ .0$2_0_old 1))
                                                    (_$2_12 (+ .01$2_0_old 1)))
                                                   (let
                                                      ((.01$2_0 _$2_12)
                                                       (.0$2_0 _$2_11)
                                                       (size$2_0 size$2_0_old)
                                                       (src$2_0 src$2_0_old))
                                                      (forall
                                                         ((result$1 Int)
                                                          (result$2 Int))
                                                         (and
                                                            (INV_42_PRE dest$1_0 i.0$1_0 size$1_0 src$1_0 .0$2_0 .01$2_0 size$2_0 src$2_0)
                                                            (=>
                                                               (INV_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 .0$2_0 .01$2_0 size$2_0 src$2_0 result$1 result$2)
                                                               (INV_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (src$1_0_old Int)
       (size$1_0_old Int))
      (=>
         (INV_REC_memcpy__1_PRE dest$1_0_old src$1_0_old size$1_0_old)
         (let
            ((i.0$1_0 0)
             (dest$1_0 dest$1_0_old)
             (size$1_0 size$1_0_old)
             (src$1_0 src$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_42__1 dest$1_0 i.0$1_0 size$1_0 src$1_0 result$1)
                  (INV_REC_memcpy__1 dest$1_0_old src$1_0_old size$1_0_old result$1)))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int))
      (=>
         (INV_42__1_PRE dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old size$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 1))
                  (INV_42__1 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old result$1)))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int))
      (=>
         (INV_42__1_PRE dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old size$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ src$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ dest$1_0_old _$1_8)))
                           (let
                              ((HEAP$1 (store HEAP$1_old _$1_9 _$1_7))
                               (_$1_10 (+ i.0$1_0_old 1)))
                              (let
                                 ((i.0$1_0 _$1_10)
                                  (dest$1_0 dest$1_0_old)
                                  (size$1_0 size$1_0_old)
                                  (src$1_0 src$1_0_old))
                                 (forall
                                    ((result$1 Int))
                                    (=>
                                       (INV_42__1 dest$1_0 i.0$1_0 size$1_0 src$1_0 result$1)
                                       (INV_42__1 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old result$1))))))))))))))
(assert
   (forall
      ((dest$2_0_old Int)
       (src$2_0_old Int)
       (size$2_0_old Int))
      (=>
         (INV_REC_memcpy__2_PRE dest$2_0_old src$2_0_old size$2_0_old)
         (let
            ((.01$2_0 src$2_0_old)
             (.0$2_0 dest$2_0_old)
             (size$2_0 size$2_0_old)
             (src$2_0 src$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_42__2 .0$2_0 .01$2_0 size$2_0 src$2_0 result$2)
                  (INV_REC_memcpy__2 dest$2_0_old src$2_0_old size$2_0_old result$2)))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$2_1 .01$2_0_old)
             (_$2_2 src$2_0_old))
            (let
               ((_$2_3 (- _$2_1 _$2_2)))
               (let
                  ((_$2_4 _$2_3)
                   (_$2_5 size$2_0_old))
                  (let
                     ((_$2_6 (< _$2_4 _$2_5)))
                     (=>
                        (not _$2_6)
                        (let
                           ((result$2 1))
                           (INV_42__2 .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old result$2))))))))))
(assert
   (forall
      ((.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42__2_PRE .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$2_1 .01$2_0_old)
             (_$2_2 src$2_0_old))
            (let
               ((_$2_3 (- _$2_1 _$2_2)))
               (let
                  ((_$2_4 _$2_3)
                   (_$2_5 size$2_0_old))
                  (let
                     ((_$2_6 (< _$2_4 _$2_5)))
                     (=>
                        _$2_6
                        (let
                           ((_$2_10 (select HEAP$2_old .01$2_0_old)))
                           (let
                              ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_10))
                               (_$2_11 (+ .0$2_0_old 1))
                               (_$2_12 (+ .01$2_0_old 1)))
                              (let
                                 ((.01$2_0 _$2_12)
                                  (.0$2_0 _$2_11)
                                  (size$2_0 size$2_0_old)
                                  (src$2_0 src$2_0_old))
                                 (forall
                                    ((result$2 Int))
                                    (=>
                                       (INV_42__2 .0$2_0 .01$2_0 size$2_0 src$2_0 result$2)
                                       (INV_42__2 .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old result$2))))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42_PRE dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$1_1 (< i.0$1_0_old size$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 i.0$1_0_old))
                  (let
                     ((_$1_6 (+ src$1_0_old _$1_5)))
                     (let
                        ((_$1_7 (select HEAP$1_old _$1_6))
                         (_$1_8 i.0$1_0_old))
                        (let
                           ((_$1_9 (+ dest$1_0_old _$1_8)))
                           (let
                              ((HEAP$1 (store HEAP$1_old _$1_9 _$1_7))
                               (_$1_10 (+ i.0$1_0_old 1)))
                              (let
                                 ((i.0$1_0 _$1_10)
                                  (dest$1_0 dest$1_0_old)
                                  (size$1_0 size$1_0_old)
                                  (src$1_0 src$1_0_old))
                                 (=>
                                    (and
                                       (let
                                          ((_$2_1 .01$2_0_old)
                                           (_$2_2 src$2_0_old))
                                          (let
                                             ((_$2_3 (- _$2_1 _$2_2)))
                                             (let
                                                ((_$2_4 _$2_3)
                                                 (_$2_5 size$2_0_old))
                                                (let
                                                   ((_$2_6 (< _$2_4 _$2_5)))
                                                   (=>
                                                      _$2_6
                                                      (let
                                                         ((_$2_10 (select HEAP$2_old .01$2_0_old)))
                                                         (let
                                                            ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_10))
                                                             (_$2_11 (+ .0$2_0_old 1))
                                                             (_$2_12 (+ .01$2_0_old 1)))
                                                            (let
                                                               ((.01$2_0 _$2_12)
                                                                (.0$2_0 _$2_11)
                                                                (size$2_0 size$2_0_old)
                                                                (src$2_0 src$2_0_old))
                                                               false)))))))))
                                    (forall
                                       ((result$1 Int)
                                        (result$2 Int))
                                       (and
                                          (INV_42_PRE dest$1_0 i.0$1_0 size$1_0 src$1_0 .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
                                          (=>
                                             (INV_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old result$1 result$2)
                                             (INV_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (.0$2_0_old Int)
       (.01$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int))
      (=>
         (INV_42_PRE dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old)
         (let
            ((_$2_1 .01$2_0_old)
             (_$2_2 src$2_0_old))
            (let
               ((_$2_3 (- _$2_1 _$2_2)))
               (let
                  ((_$2_4 _$2_3)
                   (_$2_5 size$2_0_old))
                  (let
                     ((_$2_6 (< _$2_4 _$2_5)))
                     (=>
                        _$2_6
                        (let
                           ((_$2_10 (select HEAP$2_old .01$2_0_old)))
                           (let
                              ((HEAP$2 (store HEAP$2_old .0$2_0_old _$2_10))
                               (_$2_11 (+ .0$2_0_old 1))
                               (_$2_12 (+ .01$2_0_old 1)))
                              (let
                                 ((.01$2_0 _$2_12)
                                  (.0$2_0 _$2_11)
                                  (size$2_0 size$2_0_old)
                                  (src$2_0 src$2_0_old))
                                 (=>
                                    (and
                                       (let
                                          ((_$1_1 (< i.0$1_0_old size$1_0_old)))
                                          (=>
                                             _$1_1
                                             (let
                                                ((_$1_5 i.0$1_0_old))
                                                (let
                                                   ((_$1_6 (+ src$1_0_old _$1_5)))
                                                   (let
                                                      ((_$1_7 (select HEAP$1_old _$1_6))
                                                       (_$1_8 i.0$1_0_old))
                                                      (let
                                                         ((_$1_9 (+ dest$1_0_old _$1_8)))
                                                         (let
                                                            ((HEAP$1 (store HEAP$1_old _$1_9 _$1_7))
                                                             (_$1_10 (+ i.0$1_0_old 1)))
                                                            (let
                                                               ((i.0$1_0 _$1_10)
                                                                (dest$1_0 dest$1_0_old)
                                                                (size$1_0 size$1_0_old)
                                                                (src$1_0 src$1_0_old))
                                                               false)))))))))
                                    (forall
                                       ((result$1 Int)
                                        (result$2 Int))
                                       (and
                                          (INV_42_PRE dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0 .01$2_0 size$2_0 src$2_0)
                                          (=>
                                             (INV_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0 .01$2_0 size$2_0 src$2_0 result$1 result$2)
                                             (INV_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old result$1 result$2))))))))))))))))
(check-sat)
(get-model)
