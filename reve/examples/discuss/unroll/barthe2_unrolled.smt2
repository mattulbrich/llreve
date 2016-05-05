(set-logic HORN)
(define-fun
   IN_INV
   ((n$1_0 Int)
    (n$2_0 Int))
   Bool
   (and
      (= n$1_0 n$2_0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(define-fun INV_MAIN_1 ((exitIndex$1_0 Int) (i.0$1_0 Int) (n$1_0 Int) (x.0$1_0 Int) (j.0$2_0 Int) (n$2_0 Int) (x.0$2_0 Int)) Bool
  (or (and (= exitIndex$1_0 1)          ;unrolled loop exited early
           (= x.0$1_0 x.0$2_0)
           (= i.0$1_0 0)
           (not (<= i.0$1_0 n$1_0))
           (= j.0$2_0 1)
           (= n$1_0 n$2_0))
      (and (= exitIndex$1_0 0)
           (= i.0$1_0 j.0$2_0)
           (= n$1_0 n$2_0)
           (= x.0$1_0 x.0$2_0))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV n$1_0_old n$2_0_old)
         (let
            ((n$1_0 n$1_0_old)
             (i.0$1_0.prolog 0))
            (let
               ((x.0$1_0.prolog 0)
                (_$1_1.prolog (<= i.0$1_0.prolog n$1_0)))
               (=>
                  _$1_1.prolog
                  (let
                     ((_$1_2.prolog (+ x.0$1_0.prolog i.0$1_0.prolog))
                      (_$1_3.prolog (+ i.0$1_0.prolog 1)))
                     (let
                        ((i.0$1_0.unr _$1_3.prolog)
                         (x.0$1_0.unr _$1_2.prolog))
                        (let
                           ((exitIndex$1_0 0)
                            (i.0$1_0 i.0$1_0.unr)
                            (x.0$1_0 x.0$1_0.unr)
                            (n$2_0 n$2_0_old)
                            (j.0$2_0 1)
                            (x.0$2_0 0))
                           (INV_MAIN_1 exitIndex$1_0 i.0$1_0 n$1_0 x.0$1_0 j.0$2_0 n$2_0 x.0$2_0))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV n$1_0_old n$2_0_old)
         (let
            ((n$1_0 n$1_0_old)
             (i.0$1_0.prolog 0))
            (let
               ((x.0$1_0.prolog 0)
                (_$1_1.prolog (<= i.0$1_0.prolog n$1_0)))
               (=>
                  (not _$1_1.prolog)
                  (let
                     ((exitIndex$1_0 1)
                      (i.0$1_0 i.0$1_0.prolog)
                      (x.0$1_0 x.0$1_0.prolog)
                      (n$2_0 n$2_0_old)
                      (j.0$2_0 1)
                      (x.0$2_0 0))
                     (INV_MAIN_1 exitIndex$1_0 i.0$1_0 n$1_0 x.0$1_0 j.0$2_0 n$2_0 x.0$2_0))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 exitIndex$1_0_old i.0$1_0_old n$1_0_old x.0$1_0_old j.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((exitIndex$1_0 exitIndex$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.0$1_0 x.0$1_0_old)
                (_$1_1 (<= i.0$1_0 n$1_0)))
               (=>
                  (= exitIndex$1_0 1)
                  (let
                     ((result$1 x.0$1_0)
                      (j.0$2_0 j.0$2_0_old)
                      (n$2_0 n$2_0_old))
                     (let
                        ((x.0$2_0 x.0$2_0_old)
                         (_$2_1 (<= j.0$2_0 n$2_0)))
                        (=>
                           (not _$2_1)
                           (let
                              ((result$2 x.0$2_0))
                              (OUT_INV result$1 result$2)))))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 exitIndex$1_0_old i.0$1_0_old n$1_0_old x.0$1_0_old j.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((exitIndex$1_0 exitIndex$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.0$1_0 x.0$1_0_old)
                (_$1_1 (<= i.0$1_0 n$1_0)))
               (=>
                  (distinct 1 exitIndex$1_0)
                  (=>
                     (not _$1_1)
                     (let
                        ((result$1 x.0$1_0)
                         (j.0$2_0 j.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((x.0$2_0 x.0$2_0_old)
                            (_$2_1 (<= j.0$2_0 n$2_0)))
                           (=>
                              (not _$2_1)
                              (let
                                 ((result$2 x.0$2_0))
                                 (OUT_INV result$1 result$2))))))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 exitIndex$1_0_old i.0$1_0_old n$1_0_old x.0$1_0_old j.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((exitIndex$1_0 exitIndex$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.0$1_0 x.0$1_0_old)
                (_$1_1 (<= i.0$1_0 n$1_0)))
               (=>
                  (distinct 1 exitIndex$1_0)
                  (=>
                     _$1_1
                     (let
                        ((_$1_2 (+ x.0$1_0 i.0$1_0))
                         (_$1_3 (+ i.0$1_0 1)))
                        (let
                           ((exitIndex$1_0 0)
                            (i.0$1_0 _$1_3)
                            (x.0$1_0 _$1_2)
                            (j.0$2_0 j.0$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((x.0$2_0 x.0$2_0_old)
                               (_$2_1 (<= j.0$2_0 n$2_0)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_2 (+ x.0$2_0 j.0$2_0))
                                     (_$2_3 (+ j.0$2_0 1)))
                                    (let
                                       ((j.0$2_0 _$2_3)
                                        (x.0$2_0 _$2_2))
                                       (INV_MAIN_1 exitIndex$1_0 i.0$1_0 n$1_0 x.0$1_0 j.0$2_0 n$2_0 x.0$2_0))))))))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 exitIndex$1_0_old i.0$1_0_old n$1_0_old x.0$1_0_old j.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((exitIndex$1_0 exitIndex$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.0$1_0 x.0$1_0_old)
                (_$1_1 (<= i.0$1_0 n$1_0)))
               (=>
                  (distinct 1 exitIndex$1_0)
                  (=>
                     _$1_1
                     (let
                        ((_$1_2 (+ x.0$1_0 i.0$1_0))
                         (_$1_3 (+ i.0$1_0 1)))
                        (let
                           ((exitIndex$1_0 0)
                            (i.0$1_0 _$1_3)
                            (x.0$1_0 _$1_2))
                           (=>
                              (and
                                 (let
                                    ((j.0$2_0 j.0$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (let
                                       ((x.0$2_0 x.0$2_0_old)
                                        (_$2_1 (<= j.0$2_0 n$2_0)))
                                       (=>
                                          _$2_1
                                          (let
                                             ((_$2_2 (+ x.0$2_0 j.0$2_0))
                                              (_$2_3 (+ j.0$2_0 1)))
                                             (let
                                                ((j.0$2_0 _$2_3)
                                                 (x.0$2_0 _$2_2))
                                                false))))))
                              (INV_MAIN_1 exitIndex$1_0 i.0$1_0 n$1_0 x.0$1_0 j.0$2_0_old n$2_0_old x.0$2_0_old)))))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (j.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 exitIndex$1_0_old i.0$1_0_old n$1_0_old x.0$1_0_old j.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((j.0$2_0 j.0$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((x.0$2_0 x.0$2_0_old)
                (_$2_1 (<= j.0$2_0 n$2_0)))
               (=>
                  _$2_1
                  (let
                     ((_$2_2 (+ x.0$2_0 j.0$2_0))
                      (_$2_3 (+ j.0$2_0 1)))
                     (let
                        ((j.0$2_0 _$2_3)
                         (x.0$2_0 _$2_2))
                        (=>
                           (and
                              (let
                                 ((exitIndex$1_0 exitIndex$1_0_old)
                                  (i.0$1_0 i.0$1_0_old)
                                  (n$1_0 n$1_0_old))
                                 (let
                                    ((x.0$1_0 x.0$1_0_old)
                                     (_$1_1 (<= i.0$1_0 n$1_0)))
                                    (=>
                                       (distinct 1 exitIndex$1_0)
                                       (=>
                                          _$1_1
                                          (let
                                             ((_$1_2 (+ x.0$1_0 i.0$1_0))
                                              (_$1_3 (+ i.0$1_0 1)))
                                             (let
                                                ((exitIndex$1_0 0)
                                                 (i.0$1_0 _$1_3)
                                                 (x.0$1_0 _$1_2))
                                                false)))))))
                           (INV_MAIN_1 exitIndex$1_0_old i.0$1_0_old n$1_0_old x.0$1_0_old j.0$2_0 n$2_0 x.0$2_0))))))))))
(check-sat)
(get-model)
