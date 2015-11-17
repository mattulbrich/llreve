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
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (and
            (= i$1_0_old i$2_0_old)
            (= j$1_0_old j$2_0_old))
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 j$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (= i$2_0_old 0)))
                     (=>
                        _$2_0
                        (let
                           ((r.2$2_0 j$2_0_old))
                           (let
                              ((result$2 r.2$2_0))
                              (= result$1 result$2)))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (and
            (= i$1_0_old i$2_0_old)
            (= j$1_0_old j$2_0_old))
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 j$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (= i$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((_$2_1 (= i$2_0_old 1)))
                           (=>
                              _$2_1
                              (let
                                 ((_$2_2 (+ j$2_0_old 1)))
                                 (let
                                    ((r.1$2_0 _$2_2))
                                    (let
                                       ((r.2$2_0 r.1$2_0))
                                       (let
                                          ((result$2 r.2$2_0))
                                          (= result$1 result$2)))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (and
            (= i$1_0_old i$2_0_old)
            (= j$1_0_old j$2_0_old))
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 j$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (= i$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((_$2_1 (= i$2_0_old 1)))
                           (=>
                              (not _$2_1)
                              (let
                                 ((_$2_3 (= i$2_0_old 2)))
                                 (=>
                                    _$2_3
                                    (let
                                       ((r.0$2_0 j$2_0_old))
                                       (let
                                          ((r.1$2_0 r.0$2_0))
                                          (let
                                             ((r.2$2_0 r.1$2_0))
                                             (let
                                                ((result$2 r.2$2_0))
                                                (= result$1 result$2)))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (and
            (= i$1_0_old i$2_0_old)
            (= j$1_0_old j$2_0_old))
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 j$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (= i$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((_$2_1 (= i$2_0_old 1)))
                           (=>
                              (not _$2_1)
                              (let
                                 ((_$2_3 (= i$2_0_old 2)))
                                 (=>
                                    (not _$2_3)
                                    (let
                                       ((_$2_4 (- i$2_0_old 1))
                                        (_$2_5 (+ j$2_0_old 1)))
                                       (and
                                          (INV_REC_f__2_PRE _$2_4 _$2_5)
                                          (forall
                                             ((_$2_6 Int))
                                             (=>
                                                (INV_REC_f__2 _$2_4 _$2_5 _$2_6)
                                                (let
                                                   ((_$2_4 (- i$2_0_old 1))
                                                    (_$2_5 (+ j$2_0_old 1))
                                                    (r.0$2_0 _$2_6))
                                                   (let
                                                      ((r.1$2_0 r.0$2_0))
                                                      (let
                                                         ((r.2$2_0 r.1$2_0))
                                                         (let
                                                            ((result$2 r.2$2_0))
                                                            (= result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (and
            (= i$1_0_old i$2_0_old)
            (= j$1_0_old j$2_0_old))
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- i$1_0_old 1))
                   (_$1_2 (+ j$1_0_old 1))
                   (_$2_0 (= i$2_0_old 0)))
                  (=>
                     _$2_0
                     (let
                        ((r.2$2_0 j$2_0_old))
                        (let
                           ((result$2 r.2$2_0))
                           (and
                              (INV_REC_f__1_PRE _$1_1 _$1_2)
                              (forall
                                 ((_$1_3 Int))
                                 (=>
                                    (INV_REC_f__1 _$1_1 _$1_2 _$1_3)
                                    (let
                                       ((_$1_1 (- i$1_0_old 1))
                                        (_$1_2 (+ j$1_0_old 1))
                                        (r.0$1_0 _$1_3))
                                       (let
                                          ((result$1 r.0$1_0))
                                          (= result$1 result$2)))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (and
            (= i$1_0_old i$2_0_old)
            (= j$1_0_old j$2_0_old))
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- i$1_0_old 1))
                   (_$1_2 (+ j$1_0_old 1))
                   (_$2_0 (= i$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (= i$2_0_old 1)))
                        (=>
                           _$2_1
                           (let
                              ((_$2_2 (+ j$2_0_old 1)))
                              (let
                                 ((r.1$2_0 _$2_2))
                                 (let
                                    ((r.2$2_0 r.1$2_0))
                                    (let
                                       ((result$2 r.2$2_0))
                                       (and
                                          (INV_REC_f__1_PRE _$1_1 _$1_2)
                                          (forall
                                             ((_$1_3 Int))
                                             (=>
                                                (INV_REC_f__1 _$1_1 _$1_2 _$1_3)
                                                (let
                                                   ((_$1_1 (- i$1_0_old 1))
                                                    (_$1_2 (+ j$1_0_old 1))
                                                    (r.0$1_0 _$1_3))
                                                   (let
                                                      ((result$1 r.0$1_0))
                                                      (= result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (and
            (= i$1_0_old i$2_0_old)
            (= j$1_0_old j$2_0_old))
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- i$1_0_old 1))
                   (_$1_2 (+ j$1_0_old 1))
                   (_$2_0 (= i$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (= i$2_0_old 1)))
                        (=>
                           (not _$2_1)
                           (let
                              ((_$2_3 (= i$2_0_old 2)))
                              (=>
                                 _$2_3
                                 (let
                                    ((r.0$2_0 j$2_0_old))
                                    (let
                                       ((r.1$2_0 r.0$2_0))
                                       (let
                                          ((r.2$2_0 r.1$2_0))
                                          (let
                                             ((result$2 r.2$2_0))
                                             (and
                                                (INV_REC_f__1_PRE _$1_1 _$1_2)
                                                (forall
                                                   ((_$1_3 Int))
                                                   (=>
                                                      (INV_REC_f__1 _$1_1 _$1_2 _$1_3)
                                                      (let
                                                         ((_$1_1 (- i$1_0_old 1))
                                                          (_$1_2 (+ j$1_0_old 1))
                                                          (r.0$1_0 _$1_3))
                                                         (let
                                                            ((result$1 r.0$1_0))
                                                            (= result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (and
            (= i$1_0_old i$2_0_old)
            (= j$1_0_old j$2_0_old))
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- i$1_0_old 1))
                   (_$1_2 (+ j$1_0_old 1))
                   (_$2_0 (= i$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (= i$2_0_old 1)))
                        (=>
                           (not _$2_1)
                           (let
                              ((_$2_3 (= i$2_0_old 2)))
                              (=>
                                 (not _$2_3)
                                 (let
                                    ((_$2_4 (- i$2_0_old 1))
                                     (_$2_5 (+ j$2_0_old 1)))
                                    (and
                                       (INV_REC_f_PRE _$1_1 _$1_2 _$2_4 _$2_5)
                                       (forall
                                          ((_$1_3 Int)
                                           (_$2_6 Int))
                                          (=>
                                             (INV_REC_f _$1_1 _$1_2 _$2_4 _$2_5 _$1_3 _$2_6)
                                             (let
                                                ((_$1_1 (- i$1_0_old 1))
                                                 (_$1_2 (+ j$1_0_old 1))
                                                 (r.0$1_0 _$1_3))
                                                (let
                                                   ((result$1 r.0$1_0)
                                                    (_$2_4 (- i$2_0_old 1))
                                                    (_$2_5 (+ j$2_0_old 1))
                                                    (r.0$2_0 _$2_6))
                                                   (let
                                                      ((r.1$2_0 r.0$2_0))
                                                      (let
                                                         ((r.2$2_0 r.1$2_0))
                                                         (let
                                                            ((result$2 r.2$2_0))
                                                            (= result$1 result$2)))))))))))))))))))))
; forbidden main
; offbyn main
; end
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 j$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (= i$2_0_old 0)))
                     (=>
                        _$2_0
                        (let
                           ((r.2$2_0 j$2_0_old))
                           (let
                              ((result$2 r.2$2_0))
                              (INV_REC_f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 j$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (= i$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((_$2_1 (= i$2_0_old 1)))
                           (=>
                              _$2_1
                              (let
                                 ((_$2_2 (+ j$2_0_old 1)))
                                 (let
                                    ((r.1$2_0 _$2_2))
                                    (let
                                       ((r.2$2_0 r.1$2_0))
                                       (let
                                          ((result$2 r.2$2_0))
                                          (INV_REC_f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 j$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (= i$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((_$2_1 (= i$2_0_old 1)))
                           (=>
                              (not _$2_1)
                              (let
                                 ((_$2_3 (= i$2_0_old 2)))
                                 (=>
                                    _$2_3
                                    (let
                                       ((r.0$2_0 j$2_0_old))
                                       (let
                                          ((r.1$2_0 r.0$2_0))
                                          (let
                                             ((r.2$2_0 r.1$2_0))
                                             (let
                                                ((result$2 r.2$2_0))
                                                (INV_REC_f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 j$1_0_old))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (= i$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((_$2_1 (= i$2_0_old 1)))
                           (=>
                              (not _$2_1)
                              (let
                                 ((_$2_3 (= i$2_0_old 2)))
                                 (=>
                                    (not _$2_3)
                                    (let
                                       ((_$2_4 (- i$2_0_old 1))
                                        (_$2_5 (+ j$2_0_old 1)))
                                       (and
                                          (INV_REC_f__2_PRE _$2_4 _$2_5)
                                          (forall
                                             ((_$2_6 Int))
                                             (=>
                                                (INV_REC_f__2 _$2_4 _$2_5 _$2_6)
                                                (let
                                                   ((_$2_4 (- i$2_0_old 1))
                                                    (_$2_5 (+ j$2_0_old 1))
                                                    (r.0$2_0 _$2_6))
                                                   (let
                                                      ((r.1$2_0 r.0$2_0))
                                                      (let
                                                         ((r.2$2_0 r.1$2_0))
                                                         (let
                                                            ((result$2 r.2$2_0))
                                                            (INV_REC_f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- i$1_0_old 1))
                   (_$1_2 (+ j$1_0_old 1))
                   (_$2_0 (= i$2_0_old 0)))
                  (=>
                     _$2_0
                     (let
                        ((r.2$2_0 j$2_0_old))
                        (let
                           ((result$2 r.2$2_0))
                           (and
                              (INV_REC_f__1_PRE _$1_1 _$1_2)
                              (forall
                                 ((_$1_3 Int))
                                 (=>
                                    (INV_REC_f__1 _$1_1 _$1_2 _$1_3)
                                    (let
                                       ((_$1_1 (- i$1_0_old 1))
                                        (_$1_2 (+ j$1_0_old 1))
                                        (r.0$1_0 _$1_3))
                                       (let
                                          ((result$1 r.0$1_0))
                                          (INV_REC_f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- i$1_0_old 1))
                   (_$1_2 (+ j$1_0_old 1))
                   (_$2_0 (= i$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (= i$2_0_old 1)))
                        (=>
                           _$2_1
                           (let
                              ((_$2_2 (+ j$2_0_old 1)))
                              (let
                                 ((r.1$2_0 _$2_2))
                                 (let
                                    ((r.2$2_0 r.1$2_0))
                                    (let
                                       ((result$2 r.2$2_0))
                                       (and
                                          (INV_REC_f__1_PRE _$1_1 _$1_2)
                                          (forall
                                             ((_$1_3 Int))
                                             (=>
                                                (INV_REC_f__1 _$1_1 _$1_2 _$1_3)
                                                (let
                                                   ((_$1_1 (- i$1_0_old 1))
                                                    (_$1_2 (+ j$1_0_old 1))
                                                    (r.0$1_0 _$1_3))
                                                   (let
                                                      ((result$1 r.0$1_0))
                                                      (INV_REC_f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- i$1_0_old 1))
                   (_$1_2 (+ j$1_0_old 1))
                   (_$2_0 (= i$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (= i$2_0_old 1)))
                        (=>
                           (not _$2_1)
                           (let
                              ((_$2_3 (= i$2_0_old 2)))
                              (=>
                                 _$2_3
                                 (let
                                    ((r.0$2_0 j$2_0_old))
                                    (let
                                       ((r.1$2_0 r.0$2_0))
                                       (let
                                          ((r.2$2_0 r.1$2_0))
                                          (let
                                             ((result$2 r.2$2_0))
                                             (and
                                                (INV_REC_f__1_PRE _$1_1 _$1_2)
                                                (forall
                                                   ((_$1_3 Int))
                                                   (=>
                                                      (INV_REC_f__1 _$1_1 _$1_2 _$1_3)
                                                      (let
                                                         ((_$1_1 (- i$1_0_old 1))
                                                          (_$1_2 (+ j$1_0_old 1))
                                                          (r.0$1_0 _$1_3))
                                                         (let
                                                            ((result$1 r.0$1_0))
                                                            (INV_REC_f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int)
       (i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f_PRE i$1_0_old j$1_0_old i$2_0_old j$2_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- i$1_0_old 1))
                   (_$1_2 (+ j$1_0_old 1))
                   (_$2_0 (= i$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (= i$2_0_old 1)))
                        (=>
                           (not _$2_1)
                           (let
                              ((_$2_3 (= i$2_0_old 2)))
                              (=>
                                 (not _$2_3)
                                 (let
                                    ((_$2_4 (- i$2_0_old 1))
                                     (_$2_5 (+ j$2_0_old 1)))
                                    (and
                                       (INV_REC_f_PRE _$1_1 _$1_2 _$2_4 _$2_5)
                                       (forall
                                          ((_$1_3 Int)
                                           (_$2_6 Int))
                                          (=>
                                             (INV_REC_f _$1_1 _$1_2 _$2_4 _$2_5 _$1_3 _$2_6)
                                             (let
                                                ((_$1_1 (- i$1_0_old 1))
                                                 (_$1_2 (+ j$1_0_old 1))
                                                 (r.0$1_0 _$1_3))
                                                (let
                                                   ((result$1 r.0$1_0)
                                                    (_$2_4 (- i$2_0_old 1))
                                                    (_$2_5 (+ j$2_0_old 1))
                                                    (r.0$2_0 _$2_6))
                                                   (let
                                                      ((r.1$2_0 r.0$2_0))
                                                      (let
                                                         ((r.2$2_0 r.1$2_0))
                                                         (let
                                                            ((result$2 r.2$2_0))
                                                            (INV_REC_f i$1_0_old j$1_0_old i$2_0_old j$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE i$1_0_old j$1_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 j$1_0_old))
                  (let
                     ((result$1 r.0$1_0))
                     (INV_REC_f__1 i$1_0_old j$1_0_old result$1))))))))
(assert
   (forall
      ((i$1_0_old Int)
       (j$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE i$1_0_old j$1_0_old)
         (let
            ((_$1_0 (= i$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- i$1_0_old 1))
                   (_$1_2 (+ j$1_0_old 1)))
                  (and
                     (INV_REC_f__1_PRE _$1_1 _$1_2)
                     (forall
                        ((_$1_3 Int))
                        (=>
                           (INV_REC_f__1 _$1_1 _$1_2 _$1_3)
                           (let
                              ((_$1_1 (- i$1_0_old 1))
                               (_$1_2 (+ j$1_0_old 1))
                               (r.0$1_0 _$1_3))
                              (let
                                 ((result$1 r.0$1_0))
                                 (INV_REC_f__1 i$1_0_old j$1_0_old result$1))))))))))))
(assert
   (forall
      ((i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE i$2_0_old j$2_0_old)
         (let
            ((_$2_0 (= i$2_0_old 0)))
            (=>
               _$2_0
               (let
                  ((r.2$2_0 j$2_0_old))
                  (let
                     ((result$2 r.2$2_0))
                     (INV_REC_f__2 i$2_0_old j$2_0_old result$2))))))))
(assert
   (forall
      ((i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE i$2_0_old j$2_0_old)
         (let
            ((_$2_0 (= i$2_0_old 0)))
            (=>
               (not _$2_0)
               (let
                  ((_$2_1 (= i$2_0_old 1)))
                  (=>
                     _$2_1
                     (let
                        ((_$2_2 (+ j$2_0_old 1)))
                        (let
                           ((r.1$2_0 _$2_2))
                           (let
                              ((r.2$2_0 r.1$2_0))
                              (let
                                 ((result$2 r.2$2_0))
                                 (INV_REC_f__2 i$2_0_old j$2_0_old result$2))))))))))))
(assert
   (forall
      ((i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE i$2_0_old j$2_0_old)
         (let
            ((_$2_0 (= i$2_0_old 0)))
            (=>
               (not _$2_0)
               (let
                  ((_$2_1 (= i$2_0_old 1)))
                  (=>
                     (not _$2_1)
                     (let
                        ((_$2_3 (= i$2_0_old 2)))
                        (=>
                           _$2_3
                           (let
                              ((r.0$2_0 j$2_0_old))
                              (let
                                 ((r.1$2_0 r.0$2_0))
                                 (let
                                    ((r.2$2_0 r.1$2_0))
                                    (let
                                       ((result$2 r.2$2_0))
                                       (INV_REC_f__2 i$2_0_old j$2_0_old result$2))))))))))))))
(assert
   (forall
      ((i$2_0_old Int)
       (j$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE i$2_0_old j$2_0_old)
         (let
            ((_$2_0 (= i$2_0_old 0)))
            (=>
               (not _$2_0)
               (let
                  ((_$2_1 (= i$2_0_old 1)))
                  (=>
                     (not _$2_1)
                     (let
                        ((_$2_3 (= i$2_0_old 2)))
                        (=>
                           (not _$2_3)
                           (let
                              ((_$2_4 (- i$2_0_old 1))
                               (_$2_5 (+ j$2_0_old 1)))
                              (and
                                 (INV_REC_f__2_PRE _$2_4 _$2_5)
                                 (forall
                                    ((_$2_6 Int))
                                    (=>
                                       (INV_REC_f__2 _$2_4 _$2_5 _$2_6)
                                       (let
                                          ((_$2_4 (- i$2_0_old 1))
                                           (_$2_5 (+ j$2_0_old 1))
                                           (r.0$2_0 _$2_6))
                                          (let
                                             ((r.1$2_0 r.0$2_0))
                                             (let
                                                ((r.2$2_0 r.1$2_0))
                                                (let
                                                   ((result$2 r.2$2_0))
                                                   (INV_REC_f__2 i$2_0_old j$2_0_old result$2))))))))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(check-sat)
(get-model)
