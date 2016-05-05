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
(define-fun INV_MAIN_1 ((i$1 Int) (n$1 Int) (x$1 Int) (i$2 Int) (n$2 Int) (x$2 Int)) Bool
  (and (= n$1 n$2) (= i$1 i$2) (= x$1 x$2)))
(define-fun INV_MAIN_3 ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int)) Bool
  (and (= A D) (= E B) (= C F) (= C F)))
(define-fun INV_MAIN_2 ((exitIndex$1_0 Int) (i.1$1_0 Int) (n$1_0 Int) (x.1$1_0 Int) (x.1$1_0.prolog Int) (i.1$2_0 Int) (n$2_0 Int) (x.1$2_0 Int)) Bool
  (or (and (= exitIndex$1_0 1) (= n$1_0 n$2_0) (= x.1$1_0 x.1$2_0) (= x.1$1_0.prolog x.1$2_0) (> i.1$2_0 (+ n$1_0 1)))
      (and (= exitIndex$1_0 0) (= i.1$1_0 i.1$2_0) (= n$1_0 n$2_0) (= x.1$1_0 x.1$2_0) (not (> i.1$2_0 (+ n$1_0 1))))))
(define-fun INV_MAIN_4 ((A Int) (B Int) (C Int) (D Int) (E Int)) Bool
  (or (and (= B 0) (= D (+ A 1)) (= C (+ D E)) (not (< D 0)))
      (and (= B 1) (= C E) (< D 0))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV n$1_0_old n$2_0_old)
         (let
            ((n$1_0 n$1_0_old)
             (x.0$1_0 1)
             (i.0$1_0 1)
             (n$2_0 n$2_0_old)
             (x.0$2_0 1)
             (i.0$2_0 1))
            (INV_MAIN_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.0$1_0 x.0$1_0_old)
                (_$1_1 (<= i.0$1_0 n$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 (* x.0$1_0 1))
                      (_$1_3 (+ i.0$1_0 1)))
                     (let
                        ((x.0$1_0 _$1_2)
                         (i.0$1_0 _$1_3)
                         (i.0$2_0 i.0$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((x.0$2_0 x.0$2_0_old)
                            (_$2_1 (<= i.0$2_0 n$2_0)))
                           (=>
                              _$2_1
                              (let
                                 ((_$2_2 (* x.0$2_0 1))
                                  (_$2_3 (+ i.0$2_0 1)))
                                 (let
                                    ((x.0$2_0 _$2_2)
                                     (i.0$2_0 _$2_3))
                                    (INV_MAIN_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.0$1_0 x.0$1_0_old)
                (_$1_1 (<= i.0$1_0 n$1_0)))
               (=>
                  _$1_1
                  (let
                     ((_$1_2 (* x.0$1_0 1))
                      (_$1_3 (+ i.0$1_0 1)))
                     (let
                        ((x.0$1_0 _$1_2)
                         (i.0$1_0 _$1_3))
                        (=>
                           (and
                              (let
                                 ((i.0$2_0 i.0$2_0_old)
                                  (n$2_0 n$2_0_old))
                                 (let
                                    ((x.0$2_0 x.0$2_0_old)
                                     (_$2_1 (<= i.0$2_0 n$2_0)))
                                    (=>
                                       _$2_1
                                       (let
                                          ((_$2_2 (* x.0$2_0 1))
                                           (_$2_3 (+ i.0$2_0 1)))
                                          (let
                                             ((x.0$2_0 _$2_2)
                                              (i.0$2_0 _$2_3))
                                             false))))))
                           (INV_MAIN_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0_old n$2_0_old x.0$2_0_old))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((i.0$2_0 i.0$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((x.0$2_0 x.0$2_0_old)
                (_$2_1 (<= i.0$2_0 n$2_0)))
               (=>
                  _$2_1
                  (let
                     ((_$2_2 (* x.0$2_0 1))
                      (_$2_3 (+ i.0$2_0 1)))
                     (let
                        ((x.0$2_0 _$2_2)
                         (i.0$2_0 _$2_3))
                        (=>
                           (and
                              (let
                                 ((i.0$1_0 i.0$1_0_old)
                                  (n$1_0 n$1_0_old))
                                 (let
                                    ((x.0$1_0 x.0$1_0_old)
                                     (_$1_1 (<= i.0$1_0 n$1_0)))
                                    (=>
                                       _$1_1
                                       (let
                                          ((_$1_2 (* x.0$1_0 1))
                                           (_$1_3 (+ i.0$1_0 1)))
                                          (let
                                             ((x.0$1_0 _$1_2)
                                              (i.0$1_0 _$1_3))
                                             false))))))
                           (INV_MAIN_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0 n$2_0 x.0$2_0))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.0$1_0 x.0$1_0_old)
                (_$1_1 (<= i.0$1_0 n$1_0)))
               (=>
                  (not _$1_1)
                  (let
                     ((x.1$1_0.prolog x.0$1_0)
                      (i.1$1_0.prolog 0))
                     (let
                        ((_$1_5.prolog (<= i.1$1_0.prolog n$1_0)))
                        (=>
                           _$1_5.prolog
                           (let
                              ((_$1_6.prolog (+ x.1$1_0.prolog i.1$1_0.prolog))
                               (_$1_7.prolog (+ i.1$1_0.prolog 1)))
                              (let
                                 ((x.1$1_0.unr _$1_6.prolog)
                                  (i.1$1_0.unr _$1_7.prolog))
                                 (let
                                    ((exitIndex$1_0 0)
                                     (x.1$1_0 x.1$1_0.unr)
                                     (i.1$1_0 i.1$1_0.unr)
                                     (i.0$2_0 i.0$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (let
                                       ((x.0$2_0 x.0$2_0_old)
                                        (_$2_1 (<= i.0$2_0 n$2_0)))
                                       (=>
                                          (not _$2_1)
                                          (let
                                             ((x.1$2_0 x.0$2_0)
                                              (i.1$2_0 1))
                                             (INV_MAIN_2 exitIndex$1_0 i.1$1_0 n$1_0 x.1$1_0 x.1$1_0.prolog i.1$2_0 n$2_0 x.1$2_0))))))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (n$1_0_old Int)
       (x.0$1_0_old Int)
       (i.0$2_0_old Int)
       (n$2_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_MAIN_1 i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
         (let
            ((i.0$1_0 i.0$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.0$1_0 x.0$1_0_old)
                (_$1_1 (<= i.0$1_0 n$1_0)))
               (=>
                  (not _$1_1)
                  (let
                     ((x.1$1_0.prolog x.0$1_0)
                      (i.1$1_0.prolog 0))
                     (let
                        ((_$1_5.prolog (<= i.1$1_0.prolog n$1_0)))
                        (=>
                           (not _$1_5.prolog)
                           (let
                              ((exitIndex$1_0 1)
                               (x.1$1_0 x.1$1_0.prolog)
                               (i.1$1_0 i.1$1_0.prolog)
                               (i.0$2_0 i.0$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((x.0$2_0 x.0$2_0_old)
                                  (_$2_1 (<= i.0$2_0 n$2_0)))
                                 (=>
                                    (not _$2_1)
                                    (let
                                       ((x.1$2_0 x.0$2_0)
                                        (i.1$2_0 1))
                                       (INV_MAIN_2 exitIndex$1_0 i.1$1_0 n$1_0 x.1$1_0 x.1$1_0.prolog i.1$2_0 n$2_0 x.1$2_0))))))))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (x.1$1_0.prolog_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_MAIN_2 exitIndex$1_0_old i.1$1_0_old n$1_0_old x.1$1_0_old x.1$1_0.prolog_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((exitIndex$1_0 exitIndex$1_0_old)
             (i.1$1_0 i.1$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.1$1_0 x.1$1_0_old)
                (x.1$1_0.prolog x.1$1_0.prolog_old)
                (_$1_5 (<= i.1$1_0 n$1_0)))
               (=>
                  (distinct 1 exitIndex$1_0)
                  (=>
                     _$1_5
                     (let
                        ((_$1_6 (+ x.1$1_0 i.1$1_0))
                         (_$1_7 (+ i.1$1_0 1)))
                        (let
                           ((exitIndex$1_0 0)
                            (x.1$1_0 _$1_6)
                            (i.1$1_0 _$1_7)
                            (i.1$2_0 i.1$2_0_old)
                            (n$2_0 n$2_0_old))
                           (let
                              ((x.1$2_0 x.1$2_0_old)
                               (_$2_5 (<= i.1$2_0 n$2_0)))
                              (=>
                                 _$2_5
                                 (let
                                    ((_$2_6 (+ x.1$2_0 i.1$2_0))
                                     (_$2_7 (+ i.1$2_0 1)))
                                    (let
                                       ((x.1$2_0 _$2_6)
                                        (i.1$2_0 _$2_7))
                                       (INV_MAIN_2 exitIndex$1_0 i.1$1_0 n$1_0 x.1$1_0 x.1$1_0.prolog i.1$2_0 n$2_0 x.1$2_0))))))))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (x.1$1_0.prolog_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_MAIN_2 exitIndex$1_0_old i.1$1_0_old n$1_0_old x.1$1_0_old x.1$1_0.prolog_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((exitIndex$1_0 exitIndex$1_0_old)
             (i.1$1_0 i.1$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.1$1_0 x.1$1_0_old)
                (x.1$1_0.prolog x.1$1_0.prolog_old)
                (_$1_5 (<= i.1$1_0 n$1_0)))
               (=>
                  (distinct 1 exitIndex$1_0)
                  (=>
                     _$1_5
                     (let
                        ((_$1_6 (+ x.1$1_0 i.1$1_0))
                         (_$1_7 (+ i.1$1_0 1)))
                        (let
                           ((exitIndex$1_0 0)
                            (x.1$1_0 _$1_6)
                            (i.1$1_0 _$1_7))
                           (=>
                              (and
                                 (let
                                    ((i.1$2_0 i.1$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (let
                                       ((x.1$2_0 x.1$2_0_old)
                                        (_$2_5 (<= i.1$2_0 n$2_0)))
                                       (=>
                                          _$2_5
                                          (let
                                             ((_$2_6 (+ x.1$2_0 i.1$2_0))
                                              (_$2_7 (+ i.1$2_0 1)))
                                             (let
                                                ((x.1$2_0 _$2_6)
                                                 (i.1$2_0 _$2_7))
                                                false))))))
                              (INV_MAIN_2 exitIndex$1_0 i.1$1_0 n$1_0 x.1$1_0 x.1$1_0.prolog i.1$2_0_old n$2_0_old x.1$2_0_old)))))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (x.1$1_0.prolog_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_MAIN_2 exitIndex$1_0_old i.1$1_0_old n$1_0_old x.1$1_0_old x.1$1_0.prolog_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((i.1$2_0 i.1$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((x.1$2_0 x.1$2_0_old)
                (_$2_5 (<= i.1$2_0 n$2_0)))
               (=>
                  _$2_5
                  (let
                     ((_$2_6 (+ x.1$2_0 i.1$2_0))
                      (_$2_7 (+ i.1$2_0 1)))
                     (let
                        ((x.1$2_0 _$2_6)
                         (i.1$2_0 _$2_7))
                        (=>
                           (and
                              (let
                                 ((exitIndex$1_0 exitIndex$1_0_old)
                                  (i.1$1_0 i.1$1_0_old)
                                  (n$1_0 n$1_0_old))
                                 (let
                                    ((x.1$1_0 x.1$1_0_old)
                                     (x.1$1_0.prolog x.1$1_0.prolog_old)
                                     (_$1_5 (<= i.1$1_0 n$1_0)))
                                    (=>
                                       (distinct 1 exitIndex$1_0)
                                       (=>
                                          _$1_5
                                          (let
                                             ((_$1_6 (+ x.1$1_0 i.1$1_0))
                                              (_$1_7 (+ i.1$1_0 1)))
                                             (let
                                                ((exitIndex$1_0 0)
                                                 (x.1$1_0 _$1_6)
                                                 (i.1$1_0 _$1_7))
                                                false)))))))
                           (INV_MAIN_2 exitIndex$1_0_old i.1$1_0_old n$1_0_old x.1$1_0_old x.1$1_0.prolog_old i.1$2_0 n$2_0 x.1$2_0))))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (x.1$1_0.prolog_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_MAIN_2 exitIndex$1_0_old i.1$1_0_old n$1_0_old x.1$1_0_old x.1$1_0.prolog_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((exitIndex$1_0 exitIndex$1_0_old)
             (i.1$1_0 i.1$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.1$1_0 x.1$1_0_old)
                (x.1$1_0.prolog x.1$1_0.prolog_old)
                (_$1_5 (<= i.1$1_0 n$1_0)))
               (=>
                  (= exitIndex$1_0 1)
                  (let
                     ((x.2$1_0 x.1$1_0.prolog)
                      (i.2$1_0 1)
                      (i.1$2_0 i.1$2_0_old)
                      (n$2_0 n$2_0_old))
                     (let
                        ((x.1$2_0 x.1$2_0_old)
                         (_$2_5 (<= i.1$2_0 n$2_0)))
                        (=>
                           (not _$2_5)
                           (let
                              ((x.2$2_0 x.1$2_0)
                               (i.2$2_0 1))
                              (INV_MAIN_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)))))))))))
(assert
   (forall
      ((exitIndex$1_0_old Int)
       (i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (x.1$1_0.prolog_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
         (INV_MAIN_2 exitIndex$1_0_old i.1$1_0_old n$1_0_old x.1$1_0_old x.1$1_0.prolog_old i.1$2_0_old n$2_0_old x.1$2_0_old)
         (let
            ((exitIndex$1_0 exitIndex$1_0_old)
             (i.1$1_0 i.1$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.1$1_0 x.1$1_0_old)
                (x.1$1_0.prolog x.1$1_0.prolog_old)
                (_$1_5 (<= i.1$1_0 n$1_0)))
               (=>
                  (distinct 1 exitIndex$1_0)
                  (=>
                     (not _$1_5)
                     (let
                        ((x.2$1_0 x.1$1_0)
                         (i.2$1_0 1)
                         (i.1$2_0 i.1$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((x.1$2_0 x.1$2_0_old)
                            (_$2_5 (<= i.1$2_0 n$2_0)))
                           (=>
                              (not _$2_5)
                              (let
                                 ((x.2$2_0 x.1$2_0)
                                  (i.2$2_0 1))
                                 (INV_MAIN_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0))))))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_MAIN_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((i.2$1_0 i.2$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.2$1_0 x.2$1_0_old)
                (_$1_9 (<= i.2$1_0 n$1_0)))
               (=>
                  _$1_9
                  (let
                     ((_$1_10 (* x.2$1_0 2))
                      (_$1_11 (+ i.2$1_0 1)))
                     (let
                        ((x.2$1_0 _$1_10)
                         (i.2$1_0 _$1_11)
                         (i.2$2_0 i.2$2_0_old)
                         (n$2_0 n$2_0_old))
                        (let
                           ((x.2$2_0 x.2$2_0_old)
                            (_$2_9 (<= i.2$2_0 n$2_0)))
                           (=>
                              _$2_9
                              (let
                                 ((_$2_10 (* x.2$2_0 2))
                                  (_$2_11 (+ i.2$2_0 1)))
                                 (let
                                    ((x.2$2_0 _$2_10)
                                     (i.2$2_0 _$2_11))
                                    (INV_MAIN_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)))))))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_MAIN_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((i.2$1_0 i.2$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.2$1_0 x.2$1_0_old)
                (_$1_9 (<= i.2$1_0 n$1_0)))
               (=>
                  _$1_9
                  (let
                     ((_$1_10 (* x.2$1_0 2))
                      (_$1_11 (+ i.2$1_0 1)))
                     (let
                        ((x.2$1_0 _$1_10)
                         (i.2$1_0 _$1_11))
                        (=>
                           (and
                              (let
                                 ((i.2$2_0 i.2$2_0_old)
                                  (n$2_0 n$2_0_old))
                                 (let
                                    ((x.2$2_0 x.2$2_0_old)
                                     (_$2_9 (<= i.2$2_0 n$2_0)))
                                    (=>
                                       _$2_9
                                       (let
                                          ((_$2_10 (* x.2$2_0 2))
                                           (_$2_11 (+ i.2$2_0 1)))
                                          (let
                                             ((x.2$2_0 _$2_10)
                                              (i.2$2_0 _$2_11))
                                             false))))))
                           (INV_MAIN_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0_old n$2_0_old x.2$2_0_old))))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_MAIN_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((i.2$2_0 i.2$2_0_old)
             (n$2_0 n$2_0_old))
            (let
               ((x.2$2_0 x.2$2_0_old)
                (_$2_9 (<= i.2$2_0 n$2_0)))
               (=>
                  _$2_9
                  (let
                     ((_$2_10 (* x.2$2_0 2))
                      (_$2_11 (+ i.2$2_0 1)))
                     (let
                        ((x.2$2_0 _$2_10)
                         (i.2$2_0 _$2_11))
                        (=>
                           (and
                              (let
                                 ((i.2$1_0 i.2$1_0_old)
                                  (n$1_0 n$1_0_old))
                                 (let
                                    ((x.2$1_0 x.2$1_0_old)
                                     (_$1_9 (<= i.2$1_0 n$1_0)))
                                    (=>
                                       _$1_9
                                       (let
                                          ((_$1_10 (* x.2$1_0 2))
                                           (_$1_11 (+ i.2$1_0 1)))
                                          (let
                                             ((x.2$1_0 _$1_10)
                                              (i.2$1_0 _$1_11))
                                             false))))))
                           (INV_MAIN_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0 n$2_0 x.2$2_0))))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_MAIN_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((i.2$1_0 i.2$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.2$1_0 x.2$1_0_old)
                (_$1_9 (<= i.2$1_0 n$1_0)))
               (=>
                  (not _$1_9)
                  (let
                     ((x.3$1_0.prolog x.2$1_0)
                      (.0$1_0.prolog n$1_0))
                     (let
                        ((_$1_13.prolog (>= .0$1_0.prolog 0)))
                        (=>
                           _$1_13.prolog
                           (let
                              ((_$1_14.prolog (+ x.3$1_0.prolog .0$1_0.prolog))
                               (_$1_15.prolog (+ .0$1_0.prolog (- 1))))
                              (let
                                 ((x.3$1_0.unr _$1_14.prolog)
                                  (.0$1_0.unr _$1_15.prolog))
                                 (let
                                    ((exitIndex$1_01 0)
                                     (x.3$1_0 x.3$1_0.unr)
                                     (.0$1_0 .0$1_0.unr)
                                     (i.2$2_0 i.2$2_0_old)
                                     (n$2_0 n$2_0_old))
                                    (let
                                       ((x.2$2_0 x.2$2_0_old)
                                        (_$2_9 (<= i.2$2_0 n$2_0)))
                                       (=>
                                          (not _$2_9)
                                          (let
                                             ((x.3$2_0 x.2$2_0)
                                              (.0$2_0 n$2_0))
                                             (INV_MAIN_4 .0$1_0 exitIndex$1_01 x.3$1_0 .0$2_0 x.3$2_0))))))))))))))))
(assert
   (forall
      ((i.2$1_0_old Int)
       (n$1_0_old Int)
       (x.2$1_0_old Int)
       (i.2$2_0_old Int)
       (n$2_0_old Int)
       (x.2$2_0_old Int))
      (=>
         (INV_MAIN_3 i.2$1_0_old n$1_0_old x.2$1_0_old i.2$2_0_old n$2_0_old x.2$2_0_old)
         (let
            ((i.2$1_0 i.2$1_0_old)
             (n$1_0 n$1_0_old))
            (let
               ((x.2$1_0 x.2$1_0_old)
                (_$1_9 (<= i.2$1_0 n$1_0)))
               (=>
                  (not _$1_9)
                  (let
                     ((x.3$1_0.prolog x.2$1_0)
                      (.0$1_0.prolog n$1_0))
                     (let
                        ((_$1_13.prolog (>= .0$1_0.prolog 0)))
                        (=>
                           (not _$1_13.prolog)
                           (let
                              ((exitIndex$1_01 1)
                               (x.3$1_0 x.3$1_0.prolog)
                               (.0$1_0 .0$1_0.prolog)
                               (i.2$2_0 i.2$2_0_old)
                               (n$2_0 n$2_0_old))
                              (let
                                 ((x.2$2_0 x.2$2_0_old)
                                  (_$2_9 (<= i.2$2_0 n$2_0)))
                                 (=>
                                    (not _$2_9)
                                    (let
                                       ((x.3$2_0 x.2$2_0)
                                        (.0$2_0 n$2_0))
                                       (INV_MAIN_4 .0$1_0 exitIndex$1_01 x.3$1_0 .0$2_0 x.3$2_0))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (exitIndex$1_01_old Int)
       (x.3$1_0_old Int)
       (.0$2_0_old Int)
       (x.3$2_0_old Int))
      (=>
         (INV_MAIN_4 .0$1_0_old exitIndex$1_01_old x.3$1_0_old .0$2_0_old x.3$2_0_old)
         (let
            ((.0$1_0 .0$1_0_old))
            (let
               ((exitIndex$1_01 exitIndex$1_01_old)
                (x.3$1_0 x.3$1_0_old)
                (_$1_13 (>= .0$1_0 0)))
               (=>
                  (= exitIndex$1_01 1)
                  (let
                     ((result$1 x.3$1_0)
                      (.0$2_0 .0$2_0_old))
                     (let
                        ((x.3$2_0 x.3$2_0_old)
                         (_$2_13 (> .0$2_0 0)))
                        (=>
                           (not _$2_13)
                           (let
                              ((result$2 x.3$2_0))
                              (OUT_INV result$1 result$2)))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (exitIndex$1_01_old Int)
       (x.3$1_0_old Int)
       (.0$2_0_old Int)
       (x.3$2_0_old Int))
      (=>
         (INV_MAIN_4 .0$1_0_old exitIndex$1_01_old x.3$1_0_old .0$2_0_old x.3$2_0_old)
         (let
            ((.0$1_0 .0$1_0_old))
            (let
               ((exitIndex$1_01 exitIndex$1_01_old)
                (x.3$1_0 x.3$1_0_old)
                (_$1_13 (>= .0$1_0 0)))
               (=>
                  (distinct 1 exitIndex$1_01)
                  (=>
                     (not _$1_13)
                     (let
                        ((result$1 x.3$1_0)
                         (.0$2_0 .0$2_0_old))
                        (let
                           ((x.3$2_0 x.3$2_0_old)
                            (_$2_13 (> .0$2_0 0)))
                           (=>
                              (not _$2_13)
                              (let
                                 ((result$2 x.3$2_0))
                                 (OUT_INV result$1 result$2))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (exitIndex$1_01_old Int)
       (x.3$1_0_old Int)
       (.0$2_0_old Int)
       (x.3$2_0_old Int))
      (=>
         (INV_MAIN_4 .0$1_0_old exitIndex$1_01_old x.3$1_0_old .0$2_0_old x.3$2_0_old)
         (let
            ((.0$1_0 .0$1_0_old))
            (let
               ((exitIndex$1_01 exitIndex$1_01_old)
                (x.3$1_0 x.3$1_0_old)
                (_$1_13 (>= .0$1_0 0)))
               (=>
                  (distinct 1 exitIndex$1_01)
                  (=>
                     _$1_13
                     (let
                        ((_$1_14 (+ x.3$1_0 .0$1_0))
                         (_$1_15 (+ .0$1_0 (- 1))))
                        (let
                           ((exitIndex$1_01 0)
                            (x.3$1_0 _$1_14)
                            (.0$1_0 _$1_15)
                            (.0$2_0 .0$2_0_old))
                           (let
                              ((x.3$2_0 x.3$2_0_old)
                               (_$2_13 (> .0$2_0 0)))
                              (=>
                                 _$2_13
                                 (let
                                    ((_$2_14 (+ x.3$2_0 .0$2_0))
                                     (_$2_15 (+ .0$2_0 (- 1))))
                                    (let
                                       ((x.3$2_0 _$2_14)
                                        (.0$2_0 _$2_15))
                                       (INV_MAIN_4 .0$1_0 exitIndex$1_01 x.3$1_0 .0$2_0 x.3$2_0))))))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (exitIndex$1_01_old Int)
       (x.3$1_0_old Int)
       (.0$2_0_old Int)
       (x.3$2_0_old Int))
      (=>
         (INV_MAIN_4 .0$1_0_old exitIndex$1_01_old x.3$1_0_old .0$2_0_old x.3$2_0_old)
         (let
            ((.0$1_0 .0$1_0_old))
            (let
               ((exitIndex$1_01 exitIndex$1_01_old)
                (x.3$1_0 x.3$1_0_old)
                (_$1_13 (>= .0$1_0 0)))
               (=>
                  (distinct 1 exitIndex$1_01)
                  (=>
                     _$1_13
                     (let
                        ((_$1_14 (+ x.3$1_0 .0$1_0))
                         (_$1_15 (+ .0$1_0 (- 1))))
                        (let
                           ((exitIndex$1_01 0)
                            (x.3$1_0 _$1_14)
                            (.0$1_0 _$1_15))
                           (=>
                              (and
                                 (let
                                    ((.0$2_0 .0$2_0_old))
                                    (let
                                       ((x.3$2_0 x.3$2_0_old)
                                        (_$2_13 (> .0$2_0 0)))
                                       (=>
                                          _$2_13
                                          (let
                                             ((_$2_14 (+ x.3$2_0 .0$2_0))
                                              (_$2_15 (+ .0$2_0 (- 1))))
                                             (let
                                                ((x.3$2_0 _$2_14)
                                                 (.0$2_0 _$2_15))
                                                false))))))
                              (INV_MAIN_4 .0$1_0 exitIndex$1_01 x.3$1_0 .0$2_0_old x.3$2_0_old)))))))))))
(assert
   (forall
      ((.0$1_0_old Int)
       (exitIndex$1_01_old Int)
       (x.3$1_0_old Int)
       (.0$2_0_old Int)
       (x.3$2_0_old Int))
      (=>
         (INV_MAIN_4 .0$1_0_old exitIndex$1_01_old x.3$1_0_old .0$2_0_old x.3$2_0_old)
         (let
            ((.0$2_0 .0$2_0_old))
            (let
               ((x.3$2_0 x.3$2_0_old)
                (_$2_13 (> .0$2_0 0)))
               (=>
                  _$2_13
                  (let
                     ((_$2_14 (+ x.3$2_0 .0$2_0))
                      (_$2_15 (+ .0$2_0 (- 1))))
                     (let
                        ((x.3$2_0 _$2_14)
                         (.0$2_0 _$2_15))
                        (=>
                           (and
                              (let
                                 ((.0$1_0 .0$1_0_old))
                                 (let
                                    ((exitIndex$1_01 exitIndex$1_01_old)
                                     (x.3$1_0 x.3$1_0_old)
                                     (_$1_13 (>= .0$1_0 0)))
                                    (=>
                                       (distinct 1 exitIndex$1_01)
                                       (=>
                                          _$1_13
                                          (let
                                             ((_$1_14 (+ x.3$1_0 .0$1_0))
                                              (_$1_15 (+ .0$1_0 (- 1))))
                                             (let
                                                ((exitIndex$1_01 0)
                                                 (x.3$1_0 _$1_14)
                                                 (.0$1_0 _$1_15))
                                                false)))))))
                           (INV_MAIN_4 .0$1_0_old exitIndex$1_01_old x.3$1_0_old .0$2_0 x.3$2_0))))))))))
(check-sat)
(get-model)
