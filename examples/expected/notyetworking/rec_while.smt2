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
    Int)
   Bool)
(declare-fun
   INV_23_PRE
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
    Int)
   Bool)
(declare-fun
   INV_42__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_23__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_23__2_PRE
   (Int)
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
      ((n$1_0 Int)
       (z$1_0 Int)
       (n$2_0 Int)
       (z$2_0 Int)
       (result$1 Int)
       (result$2 Int))
      (=>
         (and
            (= n$1_0 n$2_0)
            (= z$1_0 z$2_0))
         (and
            (=>
               (INV_REC_f n$1_0 z$1_0 n$2_0 z$2_0 result$1 result$2)
               (= result$1 result$2))
            (INV_REC_f_PRE n$1_0 z$1_0 n$2_0 z$2_0)))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 n$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (<= n$2_0_old 0)))
                     (=>
                        _$2_0
                        (let
                           ((r.0$2_0 n$2_0_old))
                           (let
                              ((result$2 r.0$2_0))
                              (INV_REC_f n$1_0_old z$1_0_old n$2_0_old z$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((i.0$1_0 0)
                   (_$1_1 (- n$1_0_old 1)))
                  (let
                     ((_$1_2 (< i.0$1_0 _$1_1)))
                     (=>
                        (not _$1_2)
                        (let
                           ((_$2_0 (<= n$2_0_old 0)))
                           (=>
                              (not _$2_0)
                              (let
                                 ((i.0$2_0 0)
                                  (_$2_1 (- n$2_0_old 1)))
                                 (let
                                    ((_$2_2 (< i.0$2_0 _$2_1)))
                                    (=>
                                       (not _$2_2)
                                       (forall
                                          ((result$1 Int)
                                           (result$2 Int))
                                          (and
                                             (INV_23_PRE i.0$1_0 i.0$2_0)
                                             (=>
                                                (INV_23 i.0$1_0 i.0$2_0 result$1 result$2)
                                                (INV_REC_f n$1_0_old z$1_0_old n$2_0_old z$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((i.0$1_0 0)
                   (_$1_1 (- n$1_0_old 1)))
                  (let
                     ((_$1_2 (< i.0$1_0 _$1_1)))
                     (=>
                        _$1_2
                        (let
                           ((n$1_0 n$1_0_old)
                            (_$2_0 (<= n$2_0_old 0)))
                           (=>
                              (not _$2_0)
                              (let
                                 ((i.0$2_0 0)
                                  (_$2_1 (- n$2_0_old 1)))
                                 (let
                                    ((_$2_2 (< i.0$2_0 _$2_1)))
                                    (=>
                                       _$2_2
                                       (let
                                          ((n$2_0 n$2_0_old))
                                          (forall
                                             ((result$1 Int)
                                              (result$2 Int))
                                             (and
                                                (INV_42_PRE i.0$1_0 n$1_0 i.0$2_0 n$2_0)
                                                (=>
                                                   (INV_42 i.0$1_0 n$1_0 i.0$2_0 n$2_0 result$1 result$2)
                                                   (INV_REC_f n$1_0_old z$1_0_old n$2_0_old z$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_23_PRE i.0$1_0_old i.0$2_0_old)
         (and
            (INV_REC_f_PRE i.0$1_0_old 0 i.0$2_0_old 0)
            (forall
               ((_$1_6 Int)
                (_$2_6 Int))
               (=>
                  (INV_REC_f i.0$1_0_old 0 i.0$2_0_old 0 _$1_6 _$2_6)
                  (let
                     ((r.0$1_0 _$1_6))
                     (let
                        ((result$1 r.0$1_0)
                         (r.0$2_0 _$2_6))
                        (let
                           ((result$2 r.0$2_0))
                           (INV_23 i.0$1_0_old i.0$2_0_old result$1 result$2))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_4 (+ i.0$1_0_old 1)))
            (let
               ((i.0$1_0 _$1_4)
                (_$1_1 (- n$1_0_old 1)))
               (let
                  ((_$1_2 (< i.0$1_0 _$1_1)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$2_4 (+ i.0$2_0_old 1)))
                        (let
                           ((i.0$2_0 _$2_4)
                            (_$2_1 (- n$2_0_old 1)))
                           (let
                              ((_$2_2 (< i.0$2_0 _$2_1)))
                              (=>
                                 (not _$2_2)
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_23_PRE i.0$1_0 i.0$2_0)
                                       (=>
                                          (INV_23 i.0$1_0 i.0$2_0 result$1 result$2)
                                          (INV_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_4 (+ i.0$1_0_old 1)))
            (let
               ((i.0$1_0 _$1_4)
                (_$1_1 (- n$1_0_old 1)))
               (let
                  ((_$1_2 (< i.0$1_0 _$1_1)))
                  (=>
                     _$1_2
                     (let
                        ((n$1_0 n$1_0_old)
                         (_$2_4 (+ i.0$2_0_old 1)))
                        (let
                           ((i.0$2_0 _$2_4)
                            (_$2_1 (- n$2_0_old 1)))
                           (let
                              ((_$2_2 (< i.0$2_0 _$2_1)))
                              (=>
                                 _$2_2
                                 (let
                                    ((n$2_0 n$2_0_old))
                                    (forall
                                       ((result$1 Int)
                                        (result$2 Int))
                                       (and
                                          (INV_42_PRE i.0$1_0 n$1_0 i.0$2_0 n$2_0)
                                          (=>
                                             (INV_42 i.0$1_0 n$1_0 i.0$2_0 n$2_0 result$1 result$2)
                                             (INV_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE n$1_0_old z$1_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 n$1_0_old))
                  (let
                     ((result$1 r.0$1_0))
                     (INV_REC_f__1 n$1_0_old z$1_0_old result$1))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE n$1_0_old z$1_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((i.0$1_0 0)
                   (_$1_1 (- n$1_0_old 1)))
                  (let
                     ((_$1_2 (< i.0$1_0 _$1_1)))
                     (=>
                        (not _$1_2)
                        (forall
                           ((result$1 Int))
                           (=>
                              (INV_23__1 i.0$1_0 result$1)
                              (INV_REC_f__1 n$1_0_old z$1_0_old result$1)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE n$1_0_old z$1_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((i.0$1_0 0)
                   (_$1_1 (- n$1_0_old 1)))
                  (let
                     ((_$1_2 (< i.0$1_0 _$1_1)))
                     (=>
                        _$1_2
                        (let
                           ((n$1_0 n$1_0_old))
                           (forall
                              ((result$1 Int))
                              (=>
                                 (INV_42__1 i.0$1_0 n$1_0 result$1)
                                 (INV_REC_f__1 n$1_0_old z$1_0_old result$1))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int))
      (=>
         (INV_23__1_PRE i.0$1_0_old)
         (and
            (INV_REC_f__1_PRE i.0$1_0_old 0)
            (forall
               ((_$1_6 Int))
               (=>
                  (INV_REC_f__1 i.0$1_0_old 0 _$1_6)
                  (let
                     ((r.0$1_0 _$1_6))
                     (let
                        ((result$1 r.0$1_0))
                        (INV_23__1 i.0$1_0_old result$1)))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE i.0$1_0_old n$1_0_old)
         (let
            ((_$1_4 (+ i.0$1_0_old 1)))
            (let
               ((i.0$1_0 _$1_4)
                (_$1_1 (- n$1_0_old 1)))
               (let
                  ((_$1_2 (< i.0$1_0 _$1_1)))
                  (=>
                     (not _$1_2)
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_23__1 i.0$1_0 result$1)
                           (INV_42__1 i.0$1_0_old n$1_0_old result$1))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE i.0$1_0_old n$1_0_old)
         (let
            ((_$1_4 (+ i.0$1_0_old 1)))
            (let
               ((i.0$1_0 _$1_4)
                (_$1_1 (- n$1_0_old 1)))
               (let
                  ((_$1_2 (< i.0$1_0 _$1_1)))
                  (=>
                     _$1_2
                     (let
                        ((n$1_0 n$1_0_old))
                        (forall
                           ((result$1 Int))
                           (=>
                              (INV_42__1 i.0$1_0 n$1_0 result$1)
                              (INV_42__1 i.0$1_0_old n$1_0_old result$1)))))))))))
(assert
   (forall
      ((n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE n$2_0_old z$2_0_old)
         (let
            ((_$2_0 (<= n$2_0_old 0)))
            (=>
               _$2_0
               (let
                  ((r.0$2_0 n$2_0_old))
                  (let
                     ((result$2 r.0$2_0))
                     (INV_REC_f__2 n$2_0_old z$2_0_old result$2))))))))
(assert
   (forall
      ((n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE n$2_0_old z$2_0_old)
         (let
            ((_$2_0 (<= n$2_0_old 0)))
            (=>
               (not _$2_0)
               (let
                  ((i.0$2_0 0)
                   (_$2_1 (- n$2_0_old 1)))
                  (let
                     ((_$2_2 (< i.0$2_0 _$2_1)))
                     (=>
                        (not _$2_2)
                        (forall
                           ((result$2 Int))
                           (=>
                              (INV_23__2 i.0$2_0 result$2)
                              (INV_REC_f__2 n$2_0_old z$2_0_old result$2)))))))))))
(assert
   (forall
      ((n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE n$2_0_old z$2_0_old)
         (let
            ((_$2_0 (<= n$2_0_old 0)))
            (=>
               (not _$2_0)
               (let
                  ((i.0$2_0 0)
                   (_$2_1 (- n$2_0_old 1)))
                  (let
                     ((_$2_2 (< i.0$2_0 _$2_1)))
                     (=>
                        _$2_2
                        (let
                           ((n$2_0 n$2_0_old))
                           (forall
                              ((result$2 Int))
                              (=>
                                 (INV_42__2 i.0$2_0 n$2_0 result$2)
                                 (INV_REC_f__2 n$2_0_old z$2_0_old result$2))))))))))))
(assert
   (forall
      ((i.0$2_0_old Int))
      (=>
         (INV_23__2_PRE i.0$2_0_old)
         (and
            (INV_REC_f__2_PRE i.0$2_0_old 0)
            (forall
               ((_$2_6 Int))
               (=>
                  (INV_REC_f__2 i.0$2_0_old 0 _$2_6)
                  (let
                     ((r.0$2_0 _$2_6))
                     (let
                        ((result$2 r.0$2_0))
                        (INV_23__2 i.0$2_0_old result$2)))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old n$2_0_old)
         (let
            ((_$2_4 (+ i.0$2_0_old 1)))
            (let
               ((i.0$2_0 _$2_4)
                (_$2_1 (- n$2_0_old 1)))
               (let
                  ((_$2_2 (< i.0$2_0 _$2_1)))
                  (=>
                     (not _$2_2)
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_23__2 i.0$2_0 result$2)
                           (INV_42__2 i.0$2_0_old n$2_0_old result$2))))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old n$2_0_old)
         (let
            ((_$2_4 (+ i.0$2_0_old 1)))
            (let
               ((i.0$2_0 _$2_4)
                (_$2_1 (- n$2_0_old 1)))
               (let
                  ((_$2_2 (< i.0$2_0 _$2_1)))
                  (=>
                     _$2_2
                     (let
                        ((n$2_0 n$2_0_old))
                        (forall
                           ((result$2 Int))
                           (=>
                              (INV_42__2 i.0$2_0 n$2_0 result$2)
                              (INV_42__2 i.0$2_0_old n$2_0_old result$2)))))))))))
; FORBIDDEN PATHS
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 n$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (<= n$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((i.0$2_0 0)
                            (_$2_1 (- n$2_0_old 1)))
                           (let
                              ((_$2_2 (< i.0$2_0 _$2_1)))
                              (=>
                                 (not _$2_2)
                                 false)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 n$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (<= n$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((i.0$2_0 0)
                            (_$2_1 (- n$2_0_old 1)))
                           (let
                              ((_$2_2 (< i.0$2_0 _$2_1)))
                              (=>
                                 _$2_2
                                 false)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((i.0$1_0 0)
                   (_$1_1 (- n$1_0_old 1)))
                  (let
                     ((_$1_2 (< i.0$1_0 _$1_1)))
                     (=>
                        (not _$1_2)
                        (let
                           ((_$2_0 (<= n$2_0_old 0)))
                           (=>
                              _$2_0
                              (let
                                 ((r.0$2_0 n$2_0_old))
                                 (let
                                    ((result$2 r.0$2_0))
                                    false))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((i.0$1_0 0)
                   (_$1_1 (- n$1_0_old 1)))
                  (let
                     ((_$1_2 (< i.0$1_0 _$1_1)))
                     (=>
                        (not _$1_2)
                        (let
                           ((_$2_0 (<= n$2_0_old 0)))
                           (=>
                              (not _$2_0)
                              (let
                                 ((i.0$2_0 0)
                                  (_$2_1 (- n$2_0_old 1)))
                                 (let
                                    ((_$2_2 (< i.0$2_0 _$2_1)))
                                    (=>
                                       _$2_2
                                       false)))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((i.0$1_0 0)
                   (_$1_1 (- n$1_0_old 1)))
                  (let
                     ((_$1_2 (< i.0$1_0 _$1_1)))
                     (=>
                        _$1_2
                        (let
                           ((_$2_0 (<= n$2_0_old 0)))
                           (=>
                              _$2_0
                              (let
                                 ((r.0$2_0 n$2_0_old))
                                 (let
                                    ((result$2 r.0$2_0))
                                    false))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (z$1_0_old Int)
       (n$2_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old z$1_0_old n$2_0_old z$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((i.0$1_0 0)
                   (_$1_1 (- n$1_0_old 1)))
                  (let
                     ((_$1_2 (< i.0$1_0 _$1_1)))
                     (=>
                        _$1_2
                        (let
                           ((_$2_0 (<= n$2_0_old 0)))
                           (=>
                              (not _$2_0)
                              (let
                                 ((i.0$2_0 0)
                                  (_$2_1 (- n$2_0_old 1)))
                                 (let
                                    ((_$2_2 (< i.0$2_0 _$2_1)))
                                    (=>
                                       (not _$2_2)
                                       false)))))))))))))
; OFF BY N
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$1_4 (+ i.0$1_0_old 1)))
            (let
               ((i.0$1_0 _$1_4)
                (_$1_1 (- n$1_0_old 1)))
               (let
                  ((_$1_2 (< i.0$1_0 _$1_1)))
                  (=>
                     _$1_2
                     (let
                        ((n$1_0 n$1_0_old))
                        (=>
                           (and
                              (let
                                 ((_$2_4 (+ i.0$2_0_old 1)))
                                 (let
                                    ((i.0$2_0 _$2_4)
                                     (_$2_1 (- n$2_0_old 1)))
                                    (let
                                       ((_$2_2 (< i.0$2_0 _$2_1)))
                                       (=>
                                          _$2_2
                                          (let
                                             ((n$2_0 n$2_0_old))
                                             false))))))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_42_PRE i.0$1_0 n$1_0 i.0$2_0_old n$2_0_old)
                                 (=>
                                    (INV_42 i.0$1_0 n$1_0 i.0$2_0_old n$2_0_old result$1 result$2)
                                    (INV_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old)
         (let
            ((_$2_4 (+ i.0$2_0_old 1)))
            (let
               ((i.0$2_0 _$2_4)
                (_$2_1 (- n$2_0_old 1)))
               (let
                  ((_$2_2 (< i.0$2_0 _$2_1)))
                  (=>
                     _$2_2
                     (let
                        ((n$2_0 n$2_0_old))
                        (=>
                           (and
                              (let
                                 ((_$1_4 (+ i.0$1_0_old 1)))
                                 (let
                                    ((i.0$1_0 _$1_4)
                                     (_$1_1 (- n$1_0_old 1)))
                                    (let
                                       ((_$1_2 (< i.0$1_0 _$1_1)))
                                       (=>
                                          _$1_2
                                          (let
                                             ((n$1_0 n$1_0_old))
                                             false))))))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_42_PRE i.0$1_0_old n$1_0_old i.0$2_0 n$2_0)
                                 (=>
                                    (INV_42 i.0$1_0_old n$1_0_old i.0$2_0 n$2_0 result$1 result$2)
                                    (INV_42 i.0$1_0_old n$1_0_old i.0$2_0_old n$2_0_old result$1 result$2)))))))))))))
(check-sat)
(get-model)
