(define-fun
   IN_INV
   ((dest$1_0 Int)
    (src$1_0 Int)
    (size$1_0 Int)
    (HEAP$1 (Array Int Int))
    (dest$2_0 Int)
    (src$2_0 Int)
    (size$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= dest$1_0 dest$2_0)
      (= src$1_0 src$2_0)
      (= size$1_0 size$2_0)
      (= HEAP$1 HEAP$2)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (= HEAP$1 HEAP$2)))
(declare-rel
   INV_MAIN_42
   (Int
    Int
    Int
    Int
    (Array Int Int)
    Int
    Int
    Int
    Int
    (Array Int Int))
   Bool)
(declare-rel END_QUERY ())
(declare-var dest$1_0_old Int)
(declare-var dest$2_0_old Int)
(declare-var src$1_0_old Int)
(declare-var src$2_0_old Int)
(declare-var i.0$1_0_old Int)
(declare-var i.0$2_0_old Int)
(declare-var size$1_0_old Int)
(declare-var size$2_0_old Int)
(declare-var .0$2_0_old Int)
(declare-var .01$2_0_old Int)
(declare-var HEAP$1_old (Array Int Int))
(declare-var HEAP$2_old (Array Int Int))
(rule
 (=>
  (IN_INV
   dest$1_0_old
   src$1_0_old
   size$1_0_old
   HEAP$1_old
   dest$2_0_old
   src$2_0_old
   size$2_0_old
   HEAP$2_old)
  (let
      ((dest$1_0 dest$1_0_old)
       (src$1_0 src$1_0_old)
       (size$1_0 size$1_0_old)
       (HEAP$1 HEAP$1_old)
       (i.0$1_0 0)
       (dest$2_0 dest$2_0_old)
       (src$2_0 src$2_0_old))
    (let
        ((size$2_0 size$2_0_old)
         (HEAP$2 HEAP$2_old)
         (.01$2_0 src$2_0)
         (.0$2_0 dest$2_0))
      (INV_MAIN_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 HEAP$1 .0$2_0 .01$2_0 size$2_0 src$2_0 HEAP$2)))))
(rule
 (let
     ((dest$1_0 dest$1_0_old)
      (i.0$1_0 i.0$1_0_old)
      (size$1_0 size$1_0_old))
   (let
       ((src$1_0 src$1_0_old)
        (HEAP$1 HEAP$1_old)
        (_$1_1 (< i.0$1_0 size$1_0)))
     (let
         ((result$1 1)
          (HEAP$1_res HEAP$1)
          (.0$2_0 .0$2_0_old)
          (.01$2_0 .01$2_0_old)
          (size$2_0 size$2_0_old)
          (src$2_0 src$2_0_old))
       (let
           ((HEAP$2 HEAP$2_old)
            (_$2_1 .01$2_0)
            (_$2_2 src$2_0))
         (let
             ((_$2_3 (- _$2_1 _$2_2)))
           (let
               ((_$2_4 (div _$2_3 4))
                (_$2_5 size$2_0))
             (let
                 ((_$2_6 (< _$2_4 _$2_5)))
               (let
                   ((result$2 1)
                    (HEAP$2_res HEAP$2))
                 (=>
                  (and (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old HEAP$2_old)
                       (not (OUT_INV result$1 result$2 HEAP$1_res HEAP$2_res))
                       (not _$2_6)
                       (not _$1_1))
                  END_QUERY))))))))))
(rule
 (let
     ((dest$1_0 dest$1_0_old)
      (i.0$1_0 i.0$1_0_old)
      (size$1_0 size$1_0_old))
   (let
       ((src$1_0 src$1_0_old)
        (HEAP$1 HEAP$1_old)
        (_$1_1 (< i.0$1_0 size$1_0)))
     (let
         ((_$1_2 i.0$1_0))
       (let
           ((_$1_3 (+ src$1_0 (* 4 _$1_2))))
         (let
             ((_$1_4 (select HEAP$1 _$1_3))
              (_$1_5 i.0$1_0))
           (let
               ((_$1_6 (+ dest$1_0 (* 4 _$1_5))))
             (let
                 ((HEAP$1 (store HEAP$1 _$1_6 _$1_4))
                  (_$1_7 (+ i.0$1_0 1)))
               (let
                   ((i.0$1_0 _$1_7)
                    (.0$2_0 .0$2_0_old)
                    (.01$2_0 .01$2_0_old)
                    (size$2_0 size$2_0_old)
                    (src$2_0 src$2_0_old))
                 (let
                     ((HEAP$2 HEAP$2_old)
                      (_$2_1 .01$2_0)
                      (_$2_2 src$2_0))
                   (let
                       ((_$2_3 (- _$2_1 _$2_2)))
                     (let
                         ((_$2_4 (div _$2_3 4))
                          (_$2_5 size$2_0))
                       (let
                           ((_$2_6 (< _$2_4 _$2_5)))
                         (=>
                          (and _$2_6
                               _$1_1
                               (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old HEAP$2_old))
                          (let
                              ((_$2_7 (select HEAP$2 .01$2_0)))
                            (let
                                ((HEAP$2 (store HEAP$2 .0$2_0 _$2_7))
                                 (_$2_8 (+ .0$2_0 (* 4 1)))
                                 (_$2_9 (+ .01$2_0 (* 4 1))))
                              (let
                                  ((.01$2_0 _$2_9)
                                   (.0$2_0 _$2_8))
                                (INV_MAIN_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 HEAP$1 .0$2_0 .01$2_0 size$2_0 src$2_0 HEAP$2))))))))))))))))))
(rule
 (let
     ((dest$1_0 dest$1_0_old)
      (i.0$1_0 i.0$1_0_old)
      (size$1_0 size$1_0_old))
   (let
       ((src$1_0 src$1_0_old)
        (HEAP$1 HEAP$1_old)
        (_$1_1 (< i.0$1_0 size$1_0)))
     (let
         ((_$1_2 i.0$1_0))
       (let
           ((_$1_3 (+ src$1_0 (* 4 _$1_2))))
         (let
             ((_$1_4 (select HEAP$1 _$1_3))
              (_$1_5 i.0$1_0))
           (let
               ((_$1_6 (+ dest$1_0 (* 4 _$1_5))))
             (let
                 ((HEAP$1 (store HEAP$1 _$1_6 _$1_4))
                  (_$1_7 (+ i.0$1_0 1)))
               (let
                   ((i.0$1_0 _$1_7))
                 (=>
                  (and
                   _$1_1
                   (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old HEAP$2_old)
                   (let
                       ((.0$2_0 .0$2_0_old)
                        (.01$2_0 .01$2_0_old)
                        (size$2_0 size$2_0_old)
                        (src$2_0 src$2_0_old))
                     (let
                         ((HEAP$2 HEAP$2_old)
                          (_$2_1 .01$2_0)
                          (_$2_2 src$2_0))
                       (let
                           ((_$2_3 (- _$2_1 _$2_2)))
                         (let
                             ((_$2_4 (div _$2_3 4))
                              (_$2_5 size$2_0))
                           (not (< _$2_4 _$2_5)))))))
                  (INV_MAIN_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 HEAP$1 .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old HEAP$2_old)))))))))))
(rule
 (let
     ((.0$2_0 .0$2_0_old)
      (.01$2_0 .01$2_0_old)
      (size$2_0 size$2_0_old)
      (src$2_0 src$2_0_old))
   (let
       ((HEAP$2 HEAP$2_old)
        (_$2_1 .01$2_0)
        (_$2_2 src$2_0))
     (let
         ((_$2_3 (- _$2_1 _$2_2)))
       (let
           ((_$2_4 (div _$2_3 4))
            (_$2_5 size$2_0))
         (let
             ((_$2_6 (< _$2_4 _$2_5)))
           (let
               ((_$2_7 (select HEAP$2 .01$2_0)))
             (let
                 ((HEAP$2 (store HEAP$2 .0$2_0 _$2_7))
                  (_$2_8 (+ .0$2_0 (* 4 1)))
                  (_$2_9 (+ .01$2_0 (* 4 1))))
               (let
                   ((.01$2_0 _$2_9)
                    (.0$2_0 _$2_8))
                 (=>
                  (and
                   (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old .0$2_0_old .01$2_0_old size$2_0_old src$2_0_old HEAP$2_old)
                   _$2_6
                   (let
                       ((dest$1_0 dest$1_0_old)
                        (i.0$1_0 i.0$1_0_old)
                        (size$1_0 size$1_0_old))
                     (not (< i.0$1_0 size$1_0))))
                  (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old .0$2_0 .01$2_0 size$2_0 src$2_0 HEAP$2)))))))))))
(query END_QUERY :print-certificate true)
