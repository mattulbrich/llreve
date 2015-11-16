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
   INV_REC_f__2
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
   INV_42__2
   (Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((x$1_0 Int)
       (x$2_0 Int)
       (result$1 Int)
       (result$2 Int))
      (=>
         (and
            (= x$1_0 x$2_0))
         (and
            (=>
               (INV_REC_f x$1_0 x$2_0 result$1 result$2)
               (= result$1 result$2))
            (INV_REC_f_PRE x$1_0 x$2_0)))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((_$1_0 (<= i.0$1_0 10)))
               (=>
                  (not _$1_0)
                  (let
                     ((result$1 i.0$1_0)
                      (i.0$2_0 10))
                     (let
                        ((_$2_0 (>= i.0$2_0 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_5 (- 10 i.0$2_0)))
                              (let
                                 ((result$2 _$2_5))
                                 (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((_$1_0 (<= i.0$1_0 10)))
               (=>
                  _$1_0
                  (let
                     ((x$1_0 x$1_0_old)
                      (i.0$2_0 10))
                     (let
                        ((_$2_0 (>= i.0$2_0 0)))
                        (=>
                           _$2_0
                           (let
                              ((x$2_0 x$2_0_old))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_42_PRE i.0$1_0 x$1_0 i.0$2_0 x$2_0)
                                    (=>
                                       (INV_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0 result$1 result$2)
                                       (INV_REC_f x$1_0_old x$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_2 (= i.0$1_0_old x$1_0_old)))
            (=>
               _$1_2
               (let
                  ((result$1 i.0$1_0_old)
                   (_$2_2 (- 10 x$2_0_old)))
                  (let
                     ((_$2_3 (= i.0$2_0_old _$2_2)))
                     (=>
                        _$2_3
                        (let
                           ((_$2_5 (- 10 i.0$2_0_old)))
                           (let
                              ((result$2 _$2_5))
                              (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_2 (= i.0$1_0_old x$1_0_old)))
            (=>
               _$1_2
               (let
                  ((result$1 i.0$1_0_old)
                   (_$2_2 (- 10 x$2_0_old)))
                  (let
                     ((_$2_3 (= i.0$2_0_old _$2_2)))
                     (=>
                        (not _$2_3)
                        (let
                           ((_$2_4 (+ i.0$2_0_old (- 1))))
                           (let
                              ((i.0$2_0 _$2_4))
                              (let
                                 ((_$2_0 (>= i.0$2_0 0)))
                                 (=>
                                    (not _$2_0)
                                    (let
                                       ((_$2_5 (- 10 i.0$2_0)))
                                       (let
                                          ((result$2 _$2_5))
                                          (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_2 (= i.0$1_0_old x$1_0_old)))
            (=>
               (not _$1_2)
               (let
                  ((_$1_3 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_3))
                     (let
                        ((_$1_0 (<= i.0$1_0 10)))
                        (=>
                           (not _$1_0)
                           (let
                              ((result$1 i.0$1_0)
                               (_$2_2 (- 10 x$2_0_old)))
                              (let
                                 ((_$2_3 (= i.0$2_0_old _$2_2)))
                                 (=>
                                    _$2_3
                                    (let
                                       ((_$2_5 (- 10 i.0$2_0_old)))
                                       (let
                                          ((result$2 _$2_5))
                                          (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_2 (= i.0$1_0_old x$1_0_old)))
            (=>
               (not _$1_2)
               (let
                  ((_$1_3 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_3))
                     (let
                        ((_$1_0 (<= i.0$1_0 10)))
                        (=>
                           (not _$1_0)
                           (let
                              ((result$1 i.0$1_0)
                               (_$2_2 (- 10 x$2_0_old)))
                              (let
                                 ((_$2_3 (= i.0$2_0_old _$2_2)))
                                 (=>
                                    (not _$2_3)
                                    (let
                                       ((_$2_4 (+ i.0$2_0_old (- 1))))
                                       (let
                                          ((i.0$2_0 _$2_4))
                                          (let
                                             ((_$2_0 (>= i.0$2_0 0)))
                                             (=>
                                                (not _$2_0)
                                                (let
                                                   ((_$2_5 (- 10 i.0$2_0)))
                                                   (let
                                                      ((result$2 _$2_5))
                                                      (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_2 (= i.0$1_0_old x$1_0_old)))
            (=>
               (not _$1_2)
               (let
                  ((_$1_3 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_3))
                     (let
                        ((_$1_0 (<= i.0$1_0 10)))
                        (=>
                           _$1_0
                           (let
                              ((x$1_0 x$1_0_old)
                               (_$2_2 (- 10 x$2_0_old)))
                              (let
                                 ((_$2_3 (= i.0$2_0_old _$2_2)))
                                 (=>
                                    (not _$2_3)
                                    (let
                                       ((_$2_4 (+ i.0$2_0_old (- 1))))
                                       (let
                                          ((i.0$2_0 _$2_4))
                                          (let
                                             ((_$2_0 (>= i.0$2_0 0)))
                                             (=>
                                                _$2_0
                                                (let
                                                   ((x$2_0 x$2_0_old))
                                                   (forall
                                                      ((result$1 Int)
                                                       (result$2 Int))
                                                      (and
                                                         (INV_42_PRE i.0$1_0 x$1_0 i.0$2_0 x$2_0)
                                                         (=>
                                                            (INV_42 i.0$1_0 x$1_0 i.0$2_0 x$2_0 result$1 result$2)
                                                            (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((x$1_0_old Int))
      (let
         ((i.0$1_0 0))
         (let
            ((_$1_0 (<= i.0$1_0 10)))
            (=>
               (not _$1_0)
               (let
                  ((result$1 i.0$1_0))
                  (INV_REC_f__1 x$1_0_old result$1)))))))
(assert
   (forall
      ((x$1_0_old Int))
      (let
         ((i.0$1_0 0))
         (let
            ((_$1_0 (<= i.0$1_0 10)))
            (=>
               _$1_0
               (let
                  ((x$1_0 x$1_0_old))
                  (forall
                     ((result$1 Int))
                     (=>
                        (INV_42__1 i.0$1_0 x$1_0 result$1)
                        (INV_REC_f__1 x$1_0_old result$1)))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int))
      (let
         ((_$1_2 (= i.0$1_0_old x$1_0_old)))
         (=>
            _$1_2
            (let
               ((result$1 i.0$1_0_old))
               (INV_42__1 i.0$1_0_old x$1_0_old result$1))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int))
      (let
         ((_$1_2 (= i.0$1_0_old x$1_0_old)))
         (=>
            (not _$1_2)
            (let
               ((_$1_3 (+ i.0$1_0_old 1)))
               (let
                  ((i.0$1_0 _$1_3))
                  (let
                     ((_$1_0 (<= i.0$1_0 10)))
                     (=>
                        (not _$1_0)
                        (let
                           ((result$1 i.0$1_0))
                           (INV_42__1 i.0$1_0_old x$1_0_old result$1))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int))
      (let
         ((_$1_2 (= i.0$1_0_old x$1_0_old)))
         (=>
            (not _$1_2)
            (let
               ((_$1_3 (+ i.0$1_0_old 1)))
               (let
                  ((i.0$1_0 _$1_3))
                  (let
                     ((_$1_0 (<= i.0$1_0 10)))
                     (=>
                        _$1_0
                        (let
                           ((x$1_0 x$1_0_old))
                           (forall
                              ((result$1 Int))
                              (=>
                                 (INV_42__1 i.0$1_0 x$1_0 result$1)
                                 (INV_42__1 i.0$1_0_old x$1_0_old result$1))))))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (let
         ((i.0$2_0 10))
         (let
            ((_$2_0 (>= i.0$2_0 0)))
            (=>
               (not _$2_0)
               (let
                  ((_$2_5 (- 10 i.0$2_0)))
                  (let
                     ((result$2 _$2_5))
                     (INV_REC_f__2 x$2_0_old result$2))))))))
(assert
   (forall
      ((x$2_0_old Int))
      (let
         ((i.0$2_0 10))
         (let
            ((_$2_0 (>= i.0$2_0 0)))
            (=>
               _$2_0
               (let
                  ((x$2_0 x$2_0_old))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_42__2 i.0$2_0 x$2_0 result$2)
                        (INV_REC_f__2 x$2_0_old result$2)))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (x$2_0_old Int))
      (let
         ((_$2_2 (- 10 x$2_0_old)))
         (let
            ((_$2_3 (= i.0$2_0_old _$2_2)))
            (=>
               _$2_3
               (let
                  ((_$2_5 (- 10 i.0$2_0_old)))
                  (let
                     ((result$2 _$2_5))
                     (INV_42__2 i.0$2_0_old x$2_0_old result$2))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (x$2_0_old Int))
      (let
         ((_$2_2 (- 10 x$2_0_old)))
         (let
            ((_$2_3 (= i.0$2_0_old _$2_2)))
            (=>
               (not _$2_3)
               (let
                  ((_$2_4 (+ i.0$2_0_old (- 1))))
                  (let
                     ((i.0$2_0 _$2_4))
                     (let
                        ((_$2_0 (>= i.0$2_0 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_5 (- 10 i.0$2_0)))
                              (let
                                 ((result$2 _$2_5))
                                 (INV_42__2 i.0$2_0_old x$2_0_old result$2))))))))))))
(assert
   (forall
      ((i.0$2_0_old Int)
       (x$2_0_old Int))
      (let
         ((_$2_2 (- 10 x$2_0_old)))
         (let
            ((_$2_3 (= i.0$2_0_old _$2_2)))
            (=>
               (not _$2_3)
               (let
                  ((_$2_4 (+ i.0$2_0_old (- 1))))
                  (let
                     ((i.0$2_0 _$2_4))
                     (let
                        ((_$2_0 (>= i.0$2_0 0)))
                        (=>
                           _$2_0
                           (let
                              ((x$2_0 x$2_0_old))
                              (forall
                                 ((result$2 Int))
                                 (=>
                                    (INV_42__2 i.0$2_0 x$2_0 result$2)
                                    (INV_42__2 i.0$2_0_old x$2_0_old result$2)))))))))))))
; FORBIDDEN PATHS
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((_$1_0 (<= i.0$1_0 10)))
               (=>
                  (not _$1_0)
                  (let
                     ((result$1 i.0$1_0)
                      (i.0$2_0 10))
                     (let
                        ((_$2_0 (>= i.0$2_0 0)))
                        (=>
                           _$2_0
                           false)))))))))
(assert
   (forall
      ((x$1_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_REC_f_PRE x$1_0_old x$2_0_old)
         (let
            ((i.0$1_0 0))
            (let
               ((_$1_0 (<= i.0$1_0 10)))
               (=>
                  _$1_0
                  (let
                     ((i.0$2_0 10))
                     (let
                        ((_$2_0 (>= i.0$2_0 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_5 (- 10 i.0$2_0)))
                              (let
                                 ((result$2 _$2_5))
                                 false)))))))))))
; OFF BY N
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$1_2 (= i.0$1_0_old x$1_0_old)))
            (=>
               (not _$1_2)
               (let
                  ((_$1_3 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_3))
                     (let
                        ((_$1_0 (<= i.0$1_0 10)))
                        (=>
                           _$1_0
                           (let
                              ((x$1_0 x$1_0_old))
                              (=>
                                 (and
                                    (let
                                       ((_$2_2 (- 10 x$2_0_old)))
                                       (let
                                          ((_$2_3 (= i.0$2_0_old _$2_2)))
                                          (=>
                                             (not _$2_3)
                                             (let
                                                ((_$2_4 (+ i.0$2_0_old (- 1))))
                                                (let
                                                   ((i.0$2_0 _$2_4))
                                                   (let
                                                      ((_$2_0 (>= i.0$2_0 0)))
                                                      (=>
                                                         _$2_0
                                                         (let
                                                            ((x$2_0 x$2_0_old))
                                                            false)))))))))
                                 (forall
                                    ((result$1 Int)
                                     (result$2 Int))
                                    (and
                                       (INV_42_PRE i.0$1_0 x$1_0 i.0$2_0_old x$2_0_old)
                                       (=>
                                          (INV_42 i.0$1_0 x$1_0 i.0$2_0_old x$2_0_old result$1 result$2)
                                          (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2)))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (x$1_0_old Int)
       (i.0$2_0_old Int)
       (x$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old)
         (let
            ((_$2_2 (- 10 x$2_0_old)))
            (let
               ((_$2_3 (= i.0$2_0_old _$2_2)))
               (=>
                  (not _$2_3)
                  (let
                     ((_$2_4 (+ i.0$2_0_old (- 1))))
                     (let
                        ((i.0$2_0 _$2_4))
                        (let
                           ((_$2_0 (>= i.0$2_0 0)))
                           (=>
                              _$2_0
                              (let
                                 ((x$2_0 x$2_0_old))
                                 (=>
                                    (and
                                       (let
                                          ((_$1_2 (= i.0$1_0_old x$1_0_old)))
                                          (=>
                                             (not _$1_2)
                                             (let
                                                ((_$1_3 (+ i.0$1_0_old 1)))
                                                (let
                                                   ((i.0$1_0 _$1_3))
                                                   (let
                                                      ((_$1_0 (<= i.0$1_0 10)))
                                                      (=>
                                                         _$1_0
                                                         (let
                                                            ((x$1_0 x$1_0_old))
                                                            false))))))))
                                    (forall
                                       ((result$1 Int)
                                        (result$2 Int))
                                       (and
                                          (INV_42_PRE i.0$1_0_old x$1_0_old i.0$2_0 x$2_0)
                                          (=>
                                             (INV_42 i.0$1_0_old x$1_0_old i.0$2_0 x$2_0 result$1 result$2)
                                             (INV_42 i.0$1_0_old x$1_0_old i.0$2_0_old x$2_0_old result$1 result$2))))))))))))))))
(check-sat)
(get-model)
