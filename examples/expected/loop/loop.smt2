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
(declare-fun
   INV_42
   (Int
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
       (n$2_0 Int)
       (result$1 Int)
       (result$2 Int))
      (=>
         (and
            (= n$1_0 n$2_0))
         (and
            (=>
               (INV_REC_f n$1_0 n$2_0 result$1 result$2)
               (= result$1 result$2))
            (INV_REC_f_PRE n$1_0 n$2_0)))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((j.0$1_0 0)
                (_$1_0 (<= i.0$1_0 n$1_0_old)))
               (=>
                  (not _$1_0)
                  (let
                     ((result$1 j.0$1_0)
                      (i.0$2_0 n$2_0_old))
                     (let
                        ((j.0$2_0 0)
                         (_$2_0 (>= i.0$2_0 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((result$2 j.0$2_0))
                              (INV_REC_f n$1_0_old n$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((j.0$1_0 0)
                (_$1_0 (<= i.0$1_0 n$1_0_old)))
               (=>
                  _$1_0
                  (let
                     ((n$1_0 n$1_0_old)
                      (i.0$2_0 n$2_0_old))
                     (let
                        ((j.0$2_0 0)
                         (_$2_0 (>= i.0$2_0 0)))
                        (=>
                           _$2_0
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_42_PRE i.0$1_0 j.0$1_0 n$1_0 i.0$2_0 j.0$2_0)
                                 (=>
                                    (INV_42 i.0$1_0 j.0$1_0 n$1_0 i.0$2_0 j.0$2_0 result$1 result$2)
                                    (INV_REC_f n$1_0_old n$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old)
         (let
            ((_$1_2 (+ i.0$1_0_old 1)))
            (let
               ((_$1_3 (+ j.0$1_0_old 1))
                (i.0$1_0 _$1_2))
               (let
                  ((j.0$1_0 _$1_3)
                   (_$1_0 (<= i.0$1_0 n$1_0_old)))
                  (=>
                     (not _$1_0)
                     (let
                        ((result$1 j.0$1_0)
                         (_$2_2 (- i.0$2_0_old 1)))
                        (let
                           ((_$2_3 (+ j.0$2_0_old 1))
                            (i.0$2_0 _$2_2))
                           (let
                              ((j.0$2_0 _$2_3)
                               (_$2_0 (>= i.0$2_0 0)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((result$2 j.0$2_0))
                                    (INV_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old)
         (let
            ((_$1_2 (+ i.0$1_0_old 1)))
            (let
               ((_$1_3 (+ j.0$1_0_old 1))
                (i.0$1_0 _$1_2))
               (let
                  ((j.0$1_0 _$1_3)
                   (_$1_0 (<= i.0$1_0 n$1_0_old)))
                  (=>
                     _$1_0
                     (let
                        ((n$1_0 n$1_0_old)
                         (_$2_2 (- i.0$2_0_old 1)))
                        (let
                           ((_$2_3 (+ j.0$2_0_old 1))
                            (i.0$2_0 _$2_2))
                           (let
                              ((j.0$2_0 _$2_3)
                               (_$2_0 (>= i.0$2_0 0)))
                              (=>
                                 _$2_0
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_42_PRE i.0$1_0 j.0$1_0 n$1_0 i.0$2_0 j.0$2_0)
                                       (=>
                                          (INV_42 i.0$1_0 j.0$1_0 n$1_0 i.0$2_0 j.0$2_0 result$1 result$2)
                                          (INV_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE n$1_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((j.0$1_0 0)
                (_$1_0 (<= i.0$1_0 n$1_0_old)))
               (=>
                  (not _$1_0)
                  (let
                     ((result$1 j.0$1_0))
                     (INV_REC_f__1 n$1_0_old result$1))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE n$1_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((j.0$1_0 0)
                (_$1_0 (<= i.0$1_0 n$1_0_old)))
               (=>
                  _$1_0
                  (let
                     ((n$1_0 n$1_0_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_42__1 i.0$1_0 j.0$1_0 n$1_0 result$1)
                           (INV_REC_f__1 n$1_0_old result$1))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE i.0$1_0_old j.0$1_0_old n$1_0_old)
         (let
            ((_$1_2 (+ i.0$1_0_old 1)))
            (let
               ((_$1_3 (+ j.0$1_0_old 1))
                (i.0$1_0 _$1_2))
               (let
                  ((j.0$1_0 _$1_3)
                   (_$1_0 (<= i.0$1_0 n$1_0_old)))
                  (=>
                     (not _$1_0)
                     (let
                        ((result$1 j.0$1_0))
                        (INV_42__1 i.0$1_0_old j.0$1_0_old n$1_0_old result$1)))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_42__1_PRE i.0$1_0_old j.0$1_0_old n$1_0_old)
         (let
            ((_$1_2 (+ i.0$1_0_old 1)))
            (let
               ((_$1_3 (+ j.0$1_0_old 1))
                (i.0$1_0 _$1_2))
               (let
                  ((j.0$1_0 _$1_3)
                   (_$1_0 (<= i.0$1_0 n$1_0_old)))
                  (=>
                     _$1_0
                     (let
                        ((n$1_0 n$1_0_old))
                        (forall
                           ((result$1 Int))
                           (=>
                              (INV_42__1 i.0$1_0 j.0$1_0 n$1_0 result$1)
                              (INV_42__1 i.0$1_0_old j.0$1_0_old n$1_0_old result$1)))))))))))
(assert
   (forall
      ((n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE n$2_0_old)
         (let
            ((i.0$2_0 n$2_0_old))
            (let
               ((j.0$2_0 0)
                (_$2_0 (>= i.0$2_0 0)))
               (=>
                  (not _$2_0)
                  (let
                     ((result$2 j.0$2_0))
                     (INV_REC_f__2 n$2_0_old result$2))))))))
(assert
   (forall
      ((n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE n$2_0_old)
         (let
            ((i.0$2_0 n$2_0_old))
            (let
               ((j.0$2_0 0)
                (_$2_0 (>= i.0$2_0 0)))
               (=>
                  _$2_0
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_42__2 i.0$2_0 j.0$2_0 result$2)
                        (INV_REC_f__2 n$2_0_old result$2)))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old j.0$2_0_old)
         (let
            ((_$2_2 (- i.0$2_0_old 1)))
            (let
               ((_$2_3 (+ j.0$2_0_old 1))
                (i.0$2_0 _$2_2))
               (let
                  ((j.0$2_0 _$2_3)
                   (_$2_0 (>= i.0$2_0 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((result$2 j.0$2_0))
                        (INV_42__2 i.0$2_0_old j.0$2_0_old result$2)))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_42__2_PRE i.0$2_0_old j.0$2_0_old)
         (let
            ((_$2_2 (- i.0$2_0_old 1)))
            (let
               ((_$2_3 (+ j.0$2_0_old 1))
                (i.0$2_0 _$2_2))
               (let
                  ((j.0$2_0 _$2_3)
                   (_$2_0 (>= i.0$2_0 0)))
                  (=>
                     _$2_0
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_42__2 i.0$2_0 j.0$2_0 result$2)
                           (INV_42__2 i.0$2_0_old j.0$2_0_old result$2))))))))))
; FORBIDDEN PATHS
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((j.0$1_0 0)
                (_$1_0 (<= i.0$1_0 n$1_0_old)))
               (=>
                  (not _$1_0)
                  (let
                     ((result$1 j.0$1_0)
                      (i.0$2_0 n$2_0_old))
                     (let
                        ((j.0$2_0 0)
                         (_$2_0 (>= i.0$2_0 0)))
                        (=>
                           _$2_0
                           false)))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((j.0$1_0 0)
                (_$1_0 (<= i.0$1_0 n$1_0_old)))
               (=>
                  _$1_0
                  (let
                     ((i.0$2_0 n$2_0_old))
                     (let
                        ((j.0$2_0 0)
                         (_$2_0 (>= i.0$2_0 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((result$2 j.0$2_0))
                              false))))))))))
; OFF BY N
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old)
         (let
            ((_$1_2 (+ i.0$1_0_old 1)))
            (let
               ((_$1_3 (+ j.0$1_0_old 1))
                (i.0$1_0 _$1_2))
               (let
                  ((j.0$1_0 _$1_3)
                   (_$1_0 (<= i.0$1_0 n$1_0_old)))
                  (=>
                     _$1_0
                     (let
                        ((n$1_0 n$1_0_old))
                        (=>
                           (and
                              (let
                                 ((_$2_2 (- i.0$2_0_old 1)))
                                 (let
                                    ((_$2_3 (+ j.0$2_0_old 1))
                                     (i.0$2_0 _$2_2))
                                    (let
                                       ((j.0$2_0 _$2_3)
                                        (_$2_0 (>= i.0$2_0 0)))
                                       (=>
                                          _$2_0
                                          false)))))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (and
                                 (INV_42_PRE i.0$1_0 j.0$1_0 n$1_0 i.0$2_0_old j.0$2_0_old)
                                 (=>
                                    (INV_42 i.0$1_0 j.0$1_0 n$1_0 i.0$2_0_old j.0$2_0_old result$1 result$2)
                                    (INV_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old result$1 result$2)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (n$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old)
         (let
            ((_$2_2 (- i.0$2_0_old 1)))
            (let
               ((_$2_3 (+ j.0$2_0_old 1))
                (i.0$2_0 _$2_2))
               (let
                  ((j.0$2_0 _$2_3)
                   (_$2_0 (>= i.0$2_0 0)))
                  (=>
                     _$2_0
                     (=>
                        (and
                           (let
                              ((_$1_2 (+ i.0$1_0_old 1)))
                              (let
                                 ((_$1_3 (+ j.0$1_0_old 1))
                                  (i.0$1_0 _$1_2))
                                 (let
                                    ((j.0$1_0 _$1_3)
                                     (_$1_0 (<= i.0$1_0 n$1_0_old)))
                                    (=>
                                       _$1_0
                                       (let
                                          ((n$1_0 n$1_0_old))
                                          false))))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_42_PRE i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0 j.0$2_0)
                              (=>
                                 (INV_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0 j.0$2_0 result$1 result$2)
                                 (INV_42 i.0$1_0_old j.0$1_0_old n$1_0_old i.0$2_0_old j.0$2_0_old result$1 result$2))))))))))))
(check-sat)
(get-model)
