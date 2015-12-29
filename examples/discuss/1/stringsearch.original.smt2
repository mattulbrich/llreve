(set-logic HORN)
(define-fun
   pat$1
   ()
   Int
   (- 514))
(define-fun
   pat$2
   ()
   Int
   (- 514))
(define-fun
   IN_INV
   ((base$1_0 Int)
    (n$1_0 Int)
    (patBase$1_0 Int)
    (m$1_0 Int)
    (HEAP$1 (Array Int Int))
    (base$2_0 Int)
    (n$2_0 Int)
    (patBase$2_0 Int)
    (m$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= base$1_0 base$2_0)
      (= n$1_0 n$2_0)
      (= patBase$1_0 patBase$2_0)
      (= m$1_0 m$2_0)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
(declare-fun
   INV_10_MAIN
   (Int
    Int
    Int
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
   INV_11_MAIN
   (Int
    Int
    Int
    Int
    Int
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
   INV_12_MAIN
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
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
   INV_13_MAIN
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
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
(assert
   (forall
      ((base$1_0_old Int)
       (n$1_0_old Int)
       (patBase$1_0_old Int)
       (m$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (base$2_0_old Int)
       (n$2_0_old Int)
       (patBase$2_0_old Int)
       (m$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV
            base$1_0_old
            n$1_0_old
            patBase$1_0_old
            m$1_0_old
            HEAP$1_old
            base$2_0_old
            n$2_0_old
            patBase$2_0_old
            m$2_0_old
            HEAP$2_old)
         (let
            ((HEAP$2 (store HEAP$2_old (+ pat$2 (* 513 0) 0) m$2_0_old)))
            (let
               ((_$2_0 (select HEAP$2 (+ pat$2 (* 513 0) 0))))
               (let
                  ((_$2_1 (- _$2_0 1))
                   (_$2_2 (select HEAP$2 (+ pat$2 (* 513 0) 0))))
                  (let
                     ((_$2_3 _$2_2))
                     (let
                        ((_$2_4 (+ base$2_0_old _$2_3)))
                        (let
                           ((_$2_5 (+ _$2_4 (- 1)))
                            (_$2_6 n$2_0_old))
                           (let
                              ((_$2_7 (+ base$2_0_old _$2_6))
                               (i.0$2_0 0)
                               (base$2_0 base$2_0_old)
                               (n$2_0 n$2_0_old)
                               (patBase$2_0 patBase$2_0_old)
                               (m$2_0 m$2_0_old)
                               (HEAP$1 (store HEAP$1_old (+ pat$1 (* 513 0) 0) m$1_0_old)))
                              (let
                                 ((_$1_0 (select HEAP$1 (+ pat$1 (* 513 0) 0))))
                                 (let
                                    ((_$1_1 (- _$1_0 1))
                                     (_$1_2 (select HEAP$1 (+ pat$1 (* 513 0) 0))))
                                    (let
                                       ((_$1_3 _$1_2))
                                       (let
                                          ((_$1_4 (+ base$1_0_old _$1_3)))
                                          (let
                                             ((_$1_5 (+ _$1_4 (- 1)))
                                              (_$1_6 n$1_0_old))
                                             (let
                                                ((_$1_7 (+ base$1_0_old _$1_6))
                                                 (i.0$1_0 0)
                                                 (base$1_0 base$1_0_old)
                                                 (n$1_0 n$1_0_old)
                                                 (patBase$1_0 patBase$1_0_old)
                                                 (m$1_0 m$1_0_old))
                                                (forall
                                                   ((i1 Int)
                                                    (i2 Int))
                                                   (INV_10_MAIN _$1_1 _$1_5 _$1_7 i.0$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_5 _$2_7 i.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_5_old Int)
       (_$1_7_old Int)
       (i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_5_old Int)
       (_$2_7_old Int)
       (i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_10_MAIN _$1_1_old _$1_5_old _$1_7_old i.0$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_5_old _$2_7_old i.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_9 (select HEAP$2_old (+ pat$2 (* 513 0) 0))))
            (let
               ((_$2_10 (< i.0$2_0_old _$2_9)))
               (=>
                  _$2_10
                  (let
                     ((_$2_14 (select HEAP$2_old (+ pat$2 (* 513 0) 0))))
                     (let
                        ((_$2_15 (- _$2_14 1)))
                        (let
                           ((_$2_16 _$2_15))
                           (let
                              ((_$2_17 (+ (+ pat$2 (* 513 0) (* 256 1)) (* 256 0) _$2_16)))
                              (let
                                 ((_$2_18 (select HEAP$2_old _$2_17))
                                  (_$2_19 i.0$2_0_old))
                                 (let
                                    ((_$2_20 (+ _$2_7_old _$2_19)))
                                    (let
                                       ((HEAP$2 (store HEAP$2_old _$2_20 _$2_18))
                                        (_$2_21 (+ i.0$2_0_old 1)))
                                       (let
                                          ((i.0$2_0 _$2_21)
                                           (_$2_1 _$2_1_old)
                                           (_$2_5 _$2_5_old)
                                           (_$2_7 _$2_7_old)
                                           (_$1_9 (select HEAP$1_old (+ pat$1 (* 513 0) 0))))
                                          (let
                                             ((_$1_10 (< i.0$1_0_old _$1_9)))
                                             (=>
                                                _$1_10
                                                (let
                                                   ((_$1_14 (select HEAP$1_old (+ pat$1 (* 513 0) 0))))
                                                   (let
                                                      ((_$1_15 (- _$1_14 1)))
                                                      (let
                                                         ((_$1_16 _$1_15))
                                                         (let
                                                            ((_$1_17 (+ (+ pat$1 (* 513 0) (* 256 1)) (* 256 0) _$1_16)))
                                                            (let
                                                               ((_$1_18 (select HEAP$1_old _$1_17))
                                                                (_$1_19 i.0$1_0_old))
                                                               (let
                                                                  ((_$1_20 (+ _$1_7_old _$1_19)))
                                                                  (let
                                                                     ((HEAP$1 (store HEAP$1_old _$1_20 _$1_18))
                                                                      (_$1_21 (+ i.0$1_0_old 1)))
                                                                     (let
                                                                        ((i.0$1_0 _$1_21)
                                                                         (_$1_1 _$1_1_old)
                                                                         (_$1_5 _$1_5_old)
                                                                         (_$1_7 _$1_7_old))
                                                                        (forall
                                                                           ((i1 Int)
                                                                            (i2 Int))
                                                                           (INV_10_MAIN _$1_1 _$1_5 _$1_7 i.0$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_5 _$2_7 i.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_5_old Int)
       (_$1_7_old Int)
       (i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_5_old Int)
       (_$2_7_old Int)
       (i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_10_MAIN _$1_1_old _$1_5_old _$1_7_old i.0$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_5_old _$2_7_old i.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_9 (select HEAP$2_old (+ pat$2 (* 513 0) 0))))
            (let
               ((_$2_10 (< i.0$2_0_old _$2_9)))
               (=>
                  (not _$2_10)
                  (let
                     ((_$2_22 (select HEAP$2_old (+ pat$2 (* 513 0) 0))))
                     (let
                        ((_$2_23 _$2_22))
                        (let
                           ((_$2_24 (+ (+ pat$2 (* 513 0) (* 256 1) 0) _$2_23)))
                           (let
                              ((_$2_25 (+ _$2_24 (- 1)))
                               (s.0$2_0 _$2_5_old)
                               (nmatch.0$2_0 0)
                               (_$2_1 _$2_1_old)
                               (_$2_5 _$2_5_old)
                               (_$2_7 _$2_7_old)
                               (i.0$2_0 i.0$2_0_old)
                               (HEAP$2 HEAP$2_old)
                               (_$1_9 (select HEAP$1_old (+ pat$1 (* 513 0) 0))))
                              (let
                                 ((_$1_10 (< i.0$1_0_old _$1_9)))
                                 (=>
                                    (not _$1_10)
                                    (let
                                       ((_$1_22 (select HEAP$1_old (+ pat$1 (* 513 0) 0))))
                                       (let
                                          ((_$1_23 _$1_22))
                                          (let
                                             ((_$1_24 (+ (+ pat$1 (* 513 0) (* 256 1) 0) _$1_23)))
                                             (let
                                                ((_$1_25 (+ _$1_24 (- 1)))
                                                 (s.0$1_0 _$1_5_old)
                                                 (nmatch.0$1_0 0)
                                                 (_$1_1 _$1_1_old)
                                                 (_$1_5 _$1_5_old)
                                                 (_$1_7 _$1_7_old)
                                                 (i.0$1_0 i.0$1_0_old)
                                                 (HEAP$1 HEAP$1_old))
                                                (forall
                                                   ((i1 Int)
                                                    (i2 Int))
                                                   (INV_11_MAIN _$1_1 _$1_25 _$1_7 nmatch.0$1_0 s.0$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_25 _$2_7 nmatch.0$2_0 s.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (s.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (s.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_11_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old s.0$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old s.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_27 (< s.0$2_0_old _$2_7_old)))
            (=>
               (not _$2_27)
               (let
                  ((result$2 nmatch.0$2_0_old)
                   (HEAP$2_res HEAP$2_old)
                   (_$2_1 _$2_1_old)
                   (_$2_25 _$2_25_old)
                   (_$2_7 _$2_7_old)
                   (nmatch.0$2_0 nmatch.0$2_0_old)
                   (s.0$2_0 s.0$2_0_old)
                   (HEAP$2 HEAP$2_old)
                   (_$1_27 (< s.0$1_0_old _$1_7_old)))
                  (=>
                     (not _$1_27)
                     (let
                        ((result$1 nmatch.0$1_0_old)
                         (HEAP$1_res HEAP$1_old)
                         (_$1_1 _$1_1_old)
                         (_$1_25 _$1_25_old)
                         (_$1_7 _$1_7_old)
                         (nmatch.0$1_0 nmatch.0$1_0_old)
                         (s.0$1_0 s.0$1_0_old)
                         (HEAP$1 HEAP$1_old))
                        (OUT_INV
                           result$1
                           result$2
                           HEAP$1_res
                           HEAP$2_res)))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (s.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (s.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_11_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old s.0$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old s.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_27 (< s.0$2_0_old _$2_7_old)))
            (=>
               _$2_27
               (let
                  ((_$2_31 (select HEAP$2_old s.0$2_0_old)))
                  (let
                     ((_$2_32 _$2_31))
                     (let
                        ((_$2_33 (+ (+ pat$2 (* 513 0) (* 256 2) 0) _$2_32)))
                        (let
                           ((_$2_34 (select HEAP$2_old _$2_33)))
                           (let
                              ((_$2_35 _$2_34))
                              (let
                                 ((s.1$2_0 s.0$2_0_old)
                                  (k.0$2_0 _$2_35)
                                  (_$2_1 _$2_1_old)
                                  (_$2_25 _$2_25_old)
                                  (_$2_7 _$2_7_old)
                                  (nmatch.0$2_0 nmatch.0$2_0_old)
                                  (s.0$2_0 s.0$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (_$1_27 (< s.0$1_0_old _$1_7_old)))
                                 (=>
                                    _$1_27
                                    (let
                                       ((_$1_31 (select HEAP$1_old s.0$1_0_old)))
                                       (let
                                          ((_$1_32 _$1_31))
                                          (let
                                             ((_$1_33 (+ (+ pat$1 (* 513 0) (* 256 2) 0) _$1_32)))
                                             (let
                                                ((_$1_34 (select HEAP$1_old _$1_33)))
                                                (let
                                                   ((_$1_35 _$1_34))
                                                   (let
                                                      ((s.1$1_0 s.0$1_0_old)
                                                       (k.0$1_0 _$1_35)
                                                       (_$1_1 _$1_1_old)
                                                       (_$1_25 _$1_25_old)
                                                       (_$1_7 _$1_7_old)
                                                       (nmatch.0$1_0 nmatch.0$1_0_old)
                                                       (s.0$1_0 s.0$1_0_old)
                                                       (HEAP$1 HEAP$1_old))
                                                      (forall
                                                         ((i1 Int)
                                                          (i2 Int))
                                                         (INV_12_MAIN _$1_1 _$1_25 _$1_7 k.0$1_0 nmatch.0$1_0 s.1$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_25 _$2_7 k.0$2_0 nmatch.0$2_0 s.1$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (k.0$1_0_old Int)
       (nmatch.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (k.0$2_0_old Int)
       (nmatch.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_12_MAIN _$1_1_old _$1_25_old _$1_7_old k.0$1_0_old nmatch.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old k.0$2_0_old nmatch.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_38 (distinct k.0$2_0_old 0)))
            (=>
               (not _$2_38)
               (let
                  ((_$2_46 (>= s.1$2_0_old _$2_7_old)))
                  (=>
                     _$2_46
                     (let
                        ((result$2 nmatch.0$2_0_old)
                         (HEAP$2_res HEAP$2_old)
                         (_$2_1 _$2_1_old)
                         (_$2_25 _$2_25_old)
                         (_$2_7 _$2_7_old)
                         (k.0$2_0 k.0$2_0_old)
                         (nmatch.0$2_0 nmatch.0$2_0_old)
                         (s.1$2_0 s.1$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (_$1_38 (distinct k.0$1_0_old 0)))
                        (=>
                           (not _$1_38)
                           (let
                              ((_$1_46 (>= s.1$1_0_old _$1_7_old)))
                              (=>
                                 _$1_46
                                 (let
                                    ((result$1 nmatch.0$1_0_old)
                                     (HEAP$1_res HEAP$1_old)
                                     (_$1_1 _$1_1_old)
                                     (_$1_25 _$1_25_old)
                                     (_$1_7 _$1_7_old)
                                     (k.0$1_0 k.0$1_0_old)
                                     (nmatch.0$1_0 nmatch.0$1_0_old)
                                     (s.1$1_0 s.1$1_0_old)
                                     (HEAP$1 HEAP$1_old))
                                    (OUT_INV
                                       result$1
                                       result$2
                                       HEAP$1_res
                                       HEAP$2_res)))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (k.0$1_0_old Int)
       (nmatch.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (k.0$2_0_old Int)
       (nmatch.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_12_MAIN _$1_1_old _$1_25_old _$1_7_old k.0$1_0_old nmatch.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old k.0$2_0_old nmatch.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_38 (distinct k.0$2_0_old 0)))
            (=>
               _$2_38
               (let
                  ((_$2_39 k.0$2_0_old))
                  (let
                     ((_$2_40 (+ s.1$2_0_old _$2_39)))
                     (let
                        ((_$2_41 (select HEAP$2_old _$2_40)))
                        (let
                           ((_$2_42 _$2_41))
                           (let
                              ((_$2_43 (+ (+ pat$2 (* 513 0) (* 256 2) 0) _$2_42)))
                              (let
                                 ((_$2_44 (select HEAP$2_old _$2_43)))
                                 (let
                                    ((_$2_45 _$2_44))
                                    (let
                                       ((s.1$2_0 _$2_40)
                                        (k.0$2_0 _$2_45)
                                        (_$2_1 _$2_1_old)
                                        (_$2_25 _$2_25_old)
                                        (_$2_7 _$2_7_old)
                                        (nmatch.0$2_0 nmatch.0$2_0_old)
                                        (HEAP$2 HEAP$2_old)
                                        (_$1_38 (distinct k.0$1_0_old 0)))
                                       (=>
                                          _$1_38
                                          (let
                                             ((_$1_39 k.0$1_0_old))
                                             (let
                                                ((_$1_40 (+ s.1$1_0_old _$1_39)))
                                                (let
                                                   ((_$1_41 (select HEAP$1_old _$1_40)))
                                                   (let
                                                      ((_$1_42 _$1_41))
                                                      (let
                                                         ((_$1_43 (+ (+ pat$1 (* 513 0) (* 256 2) 0) _$1_42)))
                                                         (let
                                                            ((_$1_44 (select HEAP$1_old _$1_43)))
                                                            (let
                                                               ((_$1_45 _$1_44))
                                                               (let
                                                                  ((s.1$1_0 _$1_40)
                                                                   (k.0$1_0 _$1_45)
                                                                   (_$1_1 _$1_1_old)
                                                                   (_$1_25 _$1_25_old)
                                                                   (_$1_7 _$1_7_old)
                                                                   (nmatch.0$1_0 nmatch.0$1_0_old)
                                                                   (HEAP$1 HEAP$1_old))
                                                                  (forall
                                                                     ((i1 Int)
                                                                      (i2 Int))
                                                                     (INV_12_MAIN _$1_1 _$1_25 _$1_7 k.0$1_0 nmatch.0$1_0 s.1$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_25 _$2_7 k.0$2_0 nmatch.0$2_0 s.1$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (k.0$1_0_old Int)
       (nmatch.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (k.0$2_0_old Int)
       (nmatch.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_12_MAIN _$1_1_old _$1_25_old _$1_7_old k.0$1_0_old nmatch.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old k.0$2_0_old nmatch.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_38 (distinct k.0$2_0_old 0)))
            (=>
               (not _$2_38)
               (let
                  ((_$2_46 (>= s.1$2_0_old _$2_7_old)))
                  (=>
                     (not _$2_46)
                     (let
                        ((_$2_47 _$2_1_old))
                        (let
                           ((_$2_48 (- 0 _$2_47)))
                           (let
                              ((_$2_49 (+ s.1$2_0_old _$2_48)))
                              (let
                                 ((p.0$2_0 (+ pat$2 (* 513 0) (* 256 1) 0))
                                  (q.0$2_0 _$2_49)
                                  (_$2_1 _$2_1_old)
                                  (_$2_25 _$2_25_old)
                                  (_$2_7 _$2_7_old)
                                  (k.0$2_0 k.0$2_0_old)
                                  (nmatch.0$2_0 nmatch.0$2_0_old)
                                  (s.1$2_0 s.1$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (_$1_38 (distinct k.0$1_0_old 0)))
                                 (=>
                                    (not _$1_38)
                                    (let
                                       ((_$1_46 (>= s.1$1_0_old _$1_7_old)))
                                       (=>
                                          (not _$1_46)
                                          (let
                                             ((_$1_47 _$1_1_old))
                                             (let
                                                ((_$1_48 (- 0 _$1_47)))
                                                (let
                                                   ((_$1_49 (+ s.1$1_0_old _$1_48)))
                                                   (let
                                                      ((p.0$1_0 (+ pat$1 (* 513 0) (* 256 1) 0))
                                                       (q.0$1_0 _$1_49)
                                                       (_$1_1 _$1_1_old)
                                                       (_$1_25 _$1_25_old)
                                                       (_$1_7 _$1_7_old)
                                                       (k.0$1_0 k.0$1_0_old)
                                                       (nmatch.0$1_0 nmatch.0$1_0_old)
                                                       (s.1$1_0 s.1$1_0_old)
                                                       (HEAP$1 HEAP$1_old))
                                                      (forall
                                                         ((i1 Int)
                                                          (i2 Int))
                                                         (INV_13_MAIN _$1_1 _$1_25 _$1_7 nmatch.0$1_0 p.0$1_0 q.0$1_0 s.1$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_25 _$2_7 nmatch.0$2_0 p.0$2_0 q.0$2_0 s.1$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (p.0$1_0_old Int)
       (q.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (p.0$2_0_old Int)
       (q.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_13_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old p.0$1_0_old q.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old p.0$2_0_old q.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_51 (< p.0$2_0_old _$2_25_old)))
            (=>
               _$2_51
               (let
                  ((_$2_55 (+ q.0$2_0_old 1))
                   (_$2_56 (select HEAP$2_old q.0$2_0_old)))
                  (let
                     ((_$2_57 _$2_56)
                      (_$2_58 (+ p.0$2_0_old 1))
                      (_$2_59 (select HEAP$2_old p.0$2_0_old)))
                     (let
                        ((_$2_60 _$2_59))
                        (let
                           ((_$2_61 (distinct _$2_57 _$2_60)))
                           (=>
                              _$2_61
                              (let
                                 ((nmatch.1$2_0 nmatch.0$2_0_old)
                                  (_$2_63 (+ s.1$2_0_old 1)))
                                 (let
                                    ((s.0$2_0 _$2_63)
                                     (nmatch.0$2_0 nmatch.1$2_0)
                                     (_$2_1 _$2_1_old)
                                     (_$2_25 _$2_25_old)
                                     (_$2_7 _$2_7_old)
                                     (p.0$2_0 p.0$2_0_old)
                                     (q.0$2_0 q.0$2_0_old)
                                     (s.1$2_0 s.1$2_0_old)
                                     (HEAP$2 HEAP$2_old)
                                     (_$1_51 (< p.0$1_0_old _$1_25_old)))
                                    (=>
                                       _$1_51
                                       (let
                                          ((_$1_55 (+ q.0$1_0_old 1))
                                           (_$1_56 (select HEAP$1_old q.0$1_0_old)))
                                          (let
                                             ((_$1_57 _$1_56)
                                              (_$1_58 (+ p.0$1_0_old 1))
                                              (_$1_59 (select HEAP$1_old p.0$1_0_old)))
                                             (let
                                                ((_$1_60 _$1_59))
                                                (let
                                                   ((_$1_61 (distinct _$1_57 _$1_60)))
                                                   (=>
                                                      _$1_61
                                                      (let
                                                         ((nmatch.1$1_0 nmatch.0$1_0_old)
                                                          (_$1_63 (+ s.1$1_0_old 1)))
                                                         (let
                                                            ((s.0$1_0 _$1_63)
                                                             (nmatch.0$1_0 nmatch.1$1_0)
                                                             (_$1_1 _$1_1_old)
                                                             (_$1_25 _$1_25_old)
                                                             (_$1_7 _$1_7_old)
                                                             (p.0$1_0 p.0$1_0_old)
                                                             (q.0$1_0 q.0$1_0_old)
                                                             (s.1$1_0 s.1$1_0_old)
                                                             (HEAP$1 HEAP$1_old))
                                                            (forall
                                                               ((i1 Int)
                                                                (i2 Int))
                                                               (INV_11_MAIN _$1_1 _$1_25 _$1_7 nmatch.0$1_0 s.0$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_25 _$2_7 nmatch.0$2_0 s.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (p.0$1_0_old Int)
       (q.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (p.0$2_0_old Int)
       (q.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_13_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old p.0$1_0_old q.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old p.0$2_0_old q.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_51 (< p.0$2_0_old _$2_25_old)))
            (=>
               (not _$2_51)
               (let
                  ((_$2_62 (+ nmatch.0$2_0_old 1)))
                  (let
                     ((nmatch.1$2_0 _$2_62)
                      (_$2_63 (+ s.1$2_0_old 1)))
                     (let
                        ((s.0$2_0 _$2_63)
                         (nmatch.0$2_0 nmatch.1$2_0)
                         (_$2_1 _$2_1_old)
                         (_$2_25 _$2_25_old)
                         (_$2_7 _$2_7_old)
                         (p.0$2_0 p.0$2_0_old)
                         (q.0$2_0 q.0$2_0_old)
                         (s.1$2_0 s.1$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (_$1_51 (< p.0$1_0_old _$1_25_old)))
                        (=>
                           _$1_51
                           (let
                              ((_$1_55 (+ q.0$1_0_old 1))
                               (_$1_56 (select HEAP$1_old q.0$1_0_old)))
                              (let
                                 ((_$1_57 _$1_56)
                                  (_$1_58 (+ p.0$1_0_old 1))
                                  (_$1_59 (select HEAP$1_old p.0$1_0_old)))
                                 (let
                                    ((_$1_60 _$1_59))
                                    (let
                                       ((_$1_61 (distinct _$1_57 _$1_60)))
                                       (=>
                                          _$1_61
                                          (let
                                             ((nmatch.1$1_0 nmatch.0$1_0_old)
                                              (_$1_63 (+ s.1$1_0_old 1)))
                                             (let
                                                ((s.0$1_0 _$1_63)
                                                 (nmatch.0$1_0 nmatch.1$1_0)
                                                 (_$1_1 _$1_1_old)
                                                 (_$1_25 _$1_25_old)
                                                 (_$1_7 _$1_7_old)
                                                 (p.0$1_0 p.0$1_0_old)
                                                 (q.0$1_0 q.0$1_0_old)
                                                 (s.1$1_0 s.1$1_0_old)
                                                 (HEAP$1 HEAP$1_old))
                                                (forall
                                                   ((i1 Int)
                                                    (i2 Int))
                                                   (INV_11_MAIN _$1_1 _$1_25 _$1_7 nmatch.0$1_0 s.0$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_25 _$2_7 nmatch.0$2_0 s.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (p.0$1_0_old Int)
       (q.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (p.0$2_0_old Int)
       (q.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_13_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old p.0$1_0_old q.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old p.0$2_0_old q.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_51 (< p.0$2_0_old _$2_25_old)))
            (=>
               _$2_51
               (let
                  ((_$2_55 (+ q.0$2_0_old 1))
                   (_$2_56 (select HEAP$2_old q.0$2_0_old)))
                  (let
                     ((_$2_57 _$2_56)
                      (_$2_58 (+ p.0$2_0_old 1))
                      (_$2_59 (select HEAP$2_old p.0$2_0_old)))
                     (let
                        ((_$2_60 _$2_59))
                        (let
                           ((_$2_61 (distinct _$2_57 _$2_60)))
                           (=>
                              _$2_61
                              (let
                                 ((nmatch.1$2_0 nmatch.0$2_0_old)
                                  (_$2_63 (+ s.1$2_0_old 1)))
                                 (let
                                    ((s.0$2_0 _$2_63)
                                     (nmatch.0$2_0 nmatch.1$2_0)
                                     (_$2_1 _$2_1_old)
                                     (_$2_25 _$2_25_old)
                                     (_$2_7 _$2_7_old)
                                     (p.0$2_0 p.0$2_0_old)
                                     (q.0$2_0 q.0$2_0_old)
                                     (s.1$2_0 s.1$2_0_old)
                                     (HEAP$2 HEAP$2_old)
                                     (_$1_51 (< p.0$1_0_old _$1_25_old)))
                                    (=>
                                       (not _$1_51)
                                       (let
                                          ((_$1_62 (+ nmatch.0$1_0_old 1)))
                                          (let
                                             ((nmatch.1$1_0 _$1_62)
                                              (_$1_63 (+ s.1$1_0_old 1)))
                                             (let
                                                ((s.0$1_0 _$1_63)
                                                 (nmatch.0$1_0 nmatch.1$1_0)
                                                 (_$1_1 _$1_1_old)
                                                 (_$1_25 _$1_25_old)
                                                 (_$1_7 _$1_7_old)
                                                 (p.0$1_0 p.0$1_0_old)
                                                 (q.0$1_0 q.0$1_0_old)
                                                 (s.1$1_0 s.1$1_0_old)
                                                 (HEAP$1 HEAP$1_old))
                                                (forall
                                                   ((i1 Int)
                                                    (i2 Int))
                                                   (INV_11_MAIN _$1_1 _$1_25 _$1_7 nmatch.0$1_0 s.0$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_25 _$2_7 nmatch.0$2_0 s.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (p.0$1_0_old Int)
       (q.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (p.0$2_0_old Int)
       (q.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_13_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old p.0$1_0_old q.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old p.0$2_0_old q.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_51 (< p.0$2_0_old _$2_25_old)))
            (=>
               (not _$2_51)
               (let
                  ((_$2_62 (+ nmatch.0$2_0_old 1)))
                  (let
                     ((nmatch.1$2_0 _$2_62)
                      (_$2_63 (+ s.1$2_0_old 1)))
                     (let
                        ((s.0$2_0 _$2_63)
                         (nmatch.0$2_0 nmatch.1$2_0)
                         (_$2_1 _$2_1_old)
                         (_$2_25 _$2_25_old)
                         (_$2_7 _$2_7_old)
                         (p.0$2_0 p.0$2_0_old)
                         (q.0$2_0 q.0$2_0_old)
                         (s.1$2_0 s.1$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (_$1_51 (< p.0$1_0_old _$1_25_old)))
                        (=>
                           (not _$1_51)
                           (let
                              ((_$1_62 (+ nmatch.0$1_0_old 1)))
                              (let
                                 ((nmatch.1$1_0 _$1_62)
                                  (_$1_63 (+ s.1$1_0_old 1)))
                                 (let
                                    ((s.0$1_0 _$1_63)
                                     (nmatch.0$1_0 nmatch.1$1_0)
                                     (_$1_1 _$1_1_old)
                                     (_$1_25 _$1_25_old)
                                     (_$1_7 _$1_7_old)
                                     (p.0$1_0 p.0$1_0_old)
                                     (q.0$1_0 q.0$1_0_old)
                                     (s.1$1_0 s.1$1_0_old)
                                     (HEAP$1 HEAP$1_old))
                                    (forall
                                       ((i1 Int)
                                        (i2 Int))
                                       (INV_11_MAIN _$1_1 _$1_25 _$1_7 nmatch.0$1_0 s.0$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_25 _$2_7 nmatch.0$2_0 s.0$2_0 i2 (select HEAP$2 i2)))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (p.0$1_0_old Int)
       (q.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (p.0$2_0_old Int)
       (q.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_13_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old p.0$1_0_old q.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old p.0$2_0_old q.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$2_51 (< p.0$2_0_old _$2_25_old)))
            (=>
               _$2_51
               (let
                  ((_$2_55 (+ q.0$2_0_old 1))
                   (_$2_56 (select HEAP$2_old q.0$2_0_old)))
                  (let
                     ((_$2_57 _$2_56)
                      (_$2_58 (+ p.0$2_0_old 1))
                      (_$2_59 (select HEAP$2_old p.0$2_0_old)))
                     (let
                        ((_$2_60 _$2_59))
                        (let
                           ((_$2_61 (distinct _$2_57 _$2_60)))
                           (=>
                              (not _$2_61)
                              (let
                                 ((p.0$2_0 _$2_58)
                                  (q.0$2_0 _$2_55)
                                  (_$2_1 _$2_1_old)
                                  (_$2_25 _$2_25_old)
                                  (_$2_7 _$2_7_old)
                                  (nmatch.0$2_0 nmatch.0$2_0_old)
                                  (s.1$2_0 s.1$2_0_old)
                                  (HEAP$2 HEAP$2_old)
                                  (_$1_51 (< p.0$1_0_old _$1_25_old)))
                                 (=>
                                    _$1_51
                                    (let
                                       ((_$1_55 (+ q.0$1_0_old 1))
                                        (_$1_56 (select HEAP$1_old q.0$1_0_old)))
                                       (let
                                          ((_$1_57 _$1_56)
                                           (_$1_58 (+ p.0$1_0_old 1))
                                           (_$1_59 (select HEAP$1_old p.0$1_0_old)))
                                          (let
                                             ((_$1_60 _$1_59))
                                             (let
                                                ((_$1_61 (distinct _$1_57 _$1_60)))
                                                (=>
                                                   (not _$1_61)
                                                   (let
                                                      ((p.0$1_0 _$1_58)
                                                       (q.0$1_0 _$1_55)
                                                       (_$1_1 _$1_1_old)
                                                       (_$1_25 _$1_25_old)
                                                       (_$1_7 _$1_7_old)
                                                       (nmatch.0$1_0 nmatch.0$1_0_old)
                                                       (s.1$1_0 s.1$1_0_old)
                                                       (HEAP$1 HEAP$1_old))
                                                      (forall
                                                         ((i1 Int)
                                                          (i2 Int))
                                                         (INV_13_MAIN _$1_1 _$1_25 _$1_7 nmatch.0$1_0 p.0$1_0 q.0$1_0 s.1$1_0 i1 (select HEAP$1 i1) _$2_1 _$2_25 _$2_7 nmatch.0$2_0 p.0$2_0 q.0$2_0 s.1$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))
; forbidden main
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_5_old Int)
       (_$1_7_old Int)
       (i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_5_old Int)
       (_$2_7_old Int)
       (i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_10_MAIN _$1_1_old _$1_5_old _$1_7_old i.0$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_5_old _$2_7_old i.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_9 (select HEAP$1_old (+ pat$1 (* 513 0) 0))))
            (let
               ((_$1_10 (< i.0$1_0_old _$1_9)))
               (=>
                  _$1_10
                  (let
                     ((_$1_14 (select HEAP$1_old (+ pat$1 (* 513 0) 0))))
                     (let
                        ((_$1_15 (- _$1_14 1)))
                        (let
                           ((_$1_16 _$1_15))
                           (let
                              ((_$1_17 (+ (+ pat$1 (* 513 0) (* 256 1)) (* 256 0) _$1_16)))
                              (let
                                 ((_$1_18 (select HEAP$1_old _$1_17))
                                  (_$1_19 i.0$1_0_old))
                                 (let
                                    ((_$1_20 (+ _$1_7_old _$1_19)))
                                    (let
                                       ((HEAP$1 (store HEAP$1_old _$1_20 _$1_18))
                                        (_$1_21 (+ i.0$1_0_old 1)))
                                       (let
                                          ((i.0$1_0 _$1_21)
                                           (_$2_9 (select HEAP$2_old (+ pat$2 (* 513 0) 0))))
                                          (let
                                             ((_$2_10 (< i.0$2_0_old _$2_9)))
                                             (=>
                                                (not _$2_10)
                                                (let
                                                   ((_$2_22 (select HEAP$2_old (+ pat$2 (* 513 0) 0))))
                                                   (let
                                                      ((_$2_23 _$2_22))
                                                      (let
                                                         ((_$2_24 (+ (+ pat$2 (* 513 0) (* 256 1) 0) _$2_23)))
                                                         (let
                                                            ((_$2_25 (+ _$2_24 (- 1)))
                                                             (s.0$2_0 _$2_5_old)
                                                             (nmatch.0$2_0 0))
                                                            false))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_5_old Int)
       (_$1_7_old Int)
       (i.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_5_old Int)
       (_$2_7_old Int)
       (i.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_10_MAIN _$1_1_old _$1_5_old _$1_7_old i.0$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_5_old _$2_7_old i.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_9 (select HEAP$1_old (+ pat$1 (* 513 0) 0))))
            (let
               ((_$1_10 (< i.0$1_0_old _$1_9)))
               (=>
                  (not _$1_10)
                  (let
                     ((_$1_22 (select HEAP$1_old (+ pat$1 (* 513 0) 0))))
                     (let
                        ((_$1_23 _$1_22))
                        (let
                           ((_$1_24 (+ (+ pat$1 (* 513 0) (* 256 1) 0) _$1_23)))
                           (let
                              ((_$1_25 (+ _$1_24 (- 1)))
                               (s.0$1_0 _$1_5_old)
                               (nmatch.0$1_0 0)
                               (_$2_9 (select HEAP$2_old (+ pat$2 (* 513 0) 0))))
                              (let
                                 ((_$2_10 (< i.0$2_0_old _$2_9)))
                                 (=>
                                    _$2_10
                                    (let
                                       ((_$2_14 (select HEAP$2_old (+ pat$2 (* 513 0) 0))))
                                       (let
                                          ((_$2_15 (- _$2_14 1)))
                                          (let
                                             ((_$2_16 _$2_15))
                                             (let
                                                ((_$2_17 (+ (+ pat$2 (* 513 0) (* 256 1)) (* 256 0) _$2_16)))
                                                (let
                                                   ((_$2_18 (select HEAP$2_old _$2_17))
                                                    (_$2_19 i.0$2_0_old))
                                                   (let
                                                      ((_$2_20 (+ _$2_7_old _$2_19)))
                                                      (let
                                                         ((HEAP$2 (store HEAP$2_old _$2_20 _$2_18))
                                                          (_$2_21 (+ i.0$2_0_old 1)))
                                                         (let
                                                            ((i.0$2_0 _$2_21))
                                                            false))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (s.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (s.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_11_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old s.0$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old s.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_27 (< s.0$1_0_old _$1_7_old)))
            (=>
               (not _$1_27)
               (let
                  ((result$1 nmatch.0$1_0_old)
                   (HEAP$1_res HEAP$1_old)
                   (_$2_27 (< s.0$2_0_old _$2_7_old)))
                  (=>
                     _$2_27
                     (let
                        ((_$2_31 (select HEAP$2_old s.0$2_0_old)))
                        (let
                           ((_$2_32 _$2_31))
                           (let
                              ((_$2_33 (+ (+ pat$2 (* 513 0) (* 256 2) 0) _$2_32)))
                              (let
                                 ((_$2_34 (select HEAP$2_old _$2_33)))
                                 (let
                                    ((_$2_35 _$2_34))
                                    (let
                                       ((s.1$2_0 s.0$2_0_old)
                                        (k.0$2_0 _$2_35))
                                       false)))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (s.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (s.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_11_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old s.0$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old s.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_27 (< s.0$1_0_old _$1_7_old)))
            (=>
               _$1_27
               (let
                  ((_$1_31 (select HEAP$1_old s.0$1_0_old)))
                  (let
                     ((_$1_32 _$1_31))
                     (let
                        ((_$1_33 (+ (+ pat$1 (* 513 0) (* 256 2) 0) _$1_32)))
                        (let
                           ((_$1_34 (select HEAP$1_old _$1_33)))
                           (let
                              ((_$1_35 _$1_34))
                              (let
                                 ((s.1$1_0 s.0$1_0_old)
                                  (k.0$1_0 _$1_35)
                                  (_$2_27 (< s.0$2_0_old _$2_7_old)))
                                 (=>
                                    (not _$2_27)
                                    (let
                                       ((result$2 nmatch.0$2_0_old)
                                        (HEAP$2_res HEAP$2_old))
                                       false)))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (k.0$1_0_old Int)
       (nmatch.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (k.0$2_0_old Int)
       (nmatch.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_12_MAIN _$1_1_old _$1_25_old _$1_7_old k.0$1_0_old nmatch.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old k.0$2_0_old nmatch.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_38 (distinct k.0$1_0_old 0)))
            (=>
               (not _$1_38)
               (let
                  ((_$1_46 (>= s.1$1_0_old _$1_7_old)))
                  (=>
                     _$1_46
                     (let
                        ((result$1 nmatch.0$1_0_old)
                         (HEAP$1_res HEAP$1_old)
                         (_$2_38 (distinct k.0$2_0_old 0)))
                        (=>
                           _$2_38
                           (let
                              ((_$2_39 k.0$2_0_old))
                              (let
                                 ((_$2_40 (+ s.1$2_0_old _$2_39)))
                                 (let
                                    ((_$2_41 (select HEAP$2_old _$2_40)))
                                    (let
                                       ((_$2_42 _$2_41))
                                       (let
                                          ((_$2_43 (+ (+ pat$2 (* 513 0) (* 256 2) 0) _$2_42)))
                                          (let
                                             ((_$2_44 (select HEAP$2_old _$2_43)))
                                             (let
                                                ((_$2_45 _$2_44))
                                                (let
                                                   ((s.1$2_0 _$2_40)
                                                    (k.0$2_0 _$2_45))
                                                   false)))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (k.0$1_0_old Int)
       (nmatch.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (k.0$2_0_old Int)
       (nmatch.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_12_MAIN _$1_1_old _$1_25_old _$1_7_old k.0$1_0_old nmatch.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old k.0$2_0_old nmatch.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_38 (distinct k.0$1_0_old 0)))
            (=>
               (not _$1_38)
               (let
                  ((_$1_46 (>= s.1$1_0_old _$1_7_old)))
                  (=>
                     _$1_46
                     (let
                        ((result$1 nmatch.0$1_0_old)
                         (HEAP$1_res HEAP$1_old)
                         (_$2_38 (distinct k.0$2_0_old 0)))
                        (=>
                           (not _$2_38)
                           (let
                              ((_$2_46 (>= s.1$2_0_old _$2_7_old)))
                              (=>
                                 (not _$2_46)
                                 (let
                                    ((_$2_47 _$2_1_old))
                                    (let
                                       ((_$2_48 (- 0 _$2_47)))
                                       (let
                                          ((_$2_49 (+ s.1$2_0_old _$2_48)))
                                          (let
                                             ((p.0$2_0 (+ pat$2 (* 513 0) (* 256 1) 0))
                                              (q.0$2_0 _$2_49))
                                             false)))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (k.0$1_0_old Int)
       (nmatch.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (k.0$2_0_old Int)
       (nmatch.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_12_MAIN _$1_1_old _$1_25_old _$1_7_old k.0$1_0_old nmatch.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old k.0$2_0_old nmatch.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_38 (distinct k.0$1_0_old 0)))
            (=>
               _$1_38
               (let
                  ((_$1_39 k.0$1_0_old))
                  (let
                     ((_$1_40 (+ s.1$1_0_old _$1_39)))
                     (let
                        ((_$1_41 (select HEAP$1_old _$1_40)))
                        (let
                           ((_$1_42 _$1_41))
                           (let
                              ((_$1_43 (+ (+ pat$1 (* 513 0) (* 256 2) 0) _$1_42)))
                              (let
                                 ((_$1_44 (select HEAP$1_old _$1_43)))
                                 (let
                                    ((_$1_45 _$1_44))
                                    (let
                                       ((s.1$1_0 _$1_40)
                                        (k.0$1_0 _$1_45)
                                        (_$2_38 (distinct k.0$2_0_old 0)))
                                       (=>
                                          (not _$2_38)
                                          (let
                                             ((_$2_46 (>= s.1$2_0_old _$2_7_old)))
                                             (=>
                                                _$2_46
                                                (let
                                                   ((result$2 nmatch.0$2_0_old)
                                                    (HEAP$2_res HEAP$2_old))
                                                   false)))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (k.0$1_0_old Int)
       (nmatch.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (k.0$2_0_old Int)
       (nmatch.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_12_MAIN _$1_1_old _$1_25_old _$1_7_old k.0$1_0_old nmatch.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old k.0$2_0_old nmatch.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_38 (distinct k.0$1_0_old 0)))
            (=>
               _$1_38
               (let
                  ((_$1_39 k.0$1_0_old))
                  (let
                     ((_$1_40 (+ s.1$1_0_old _$1_39)))
                     (let
                        ((_$1_41 (select HEAP$1_old _$1_40)))
                        (let
                           ((_$1_42 _$1_41))
                           (let
                              ((_$1_43 (+ (+ pat$1 (* 513 0) (* 256 2) 0) _$1_42)))
                              (let
                                 ((_$1_44 (select HEAP$1_old _$1_43)))
                                 (let
                                    ((_$1_45 _$1_44))
                                    (let
                                       ((s.1$1_0 _$1_40)
                                        (k.0$1_0 _$1_45)
                                        (_$2_38 (distinct k.0$2_0_old 0)))
                                       (=>
                                          (not _$2_38)
                                          (let
                                             ((_$2_46 (>= s.1$2_0_old _$2_7_old)))
                                             (=>
                                                (not _$2_46)
                                                (let
                                                   ((_$2_47 _$2_1_old))
                                                   (let
                                                      ((_$2_48 (- 0 _$2_47)))
                                                      (let
                                                         ((_$2_49 (+ s.1$2_0_old _$2_48)))
                                                         (let
                                                            ((p.0$2_0 (+ pat$2 (* 513 0) (* 256 1) 0))
                                                             (q.0$2_0 _$2_49))
                                                            false))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (k.0$1_0_old Int)
       (nmatch.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (k.0$2_0_old Int)
       (nmatch.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_12_MAIN _$1_1_old _$1_25_old _$1_7_old k.0$1_0_old nmatch.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old k.0$2_0_old nmatch.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_38 (distinct k.0$1_0_old 0)))
            (=>
               (not _$1_38)
               (let
                  ((_$1_46 (>= s.1$1_0_old _$1_7_old)))
                  (=>
                     (not _$1_46)
                     (let
                        ((_$1_47 _$1_1_old))
                        (let
                           ((_$1_48 (- 0 _$1_47)))
                           (let
                              ((_$1_49 (+ s.1$1_0_old _$1_48)))
                              (let
                                 ((p.0$1_0 (+ pat$1 (* 513 0) (* 256 1) 0))
                                  (q.0$1_0 _$1_49)
                                  (_$2_38 (distinct k.0$2_0_old 0)))
                                 (=>
                                    (not _$2_38)
                                    (let
                                       ((_$2_46 (>= s.1$2_0_old _$2_7_old)))
                                       (=>
                                          _$2_46
                                          (let
                                             ((result$2 nmatch.0$2_0_old)
                                              (HEAP$2_res HEAP$2_old))
                                             false)))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (k.0$1_0_old Int)
       (nmatch.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (k.0$2_0_old Int)
       (nmatch.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_12_MAIN _$1_1_old _$1_25_old _$1_7_old k.0$1_0_old nmatch.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old k.0$2_0_old nmatch.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_38 (distinct k.0$1_0_old 0)))
            (=>
               (not _$1_38)
               (let
                  ((_$1_46 (>= s.1$1_0_old _$1_7_old)))
                  (=>
                     (not _$1_46)
                     (let
                        ((_$1_47 _$1_1_old))
                        (let
                           ((_$1_48 (- 0 _$1_47)))
                           (let
                              ((_$1_49 (+ s.1$1_0_old _$1_48)))
                              (let
                                 ((p.0$1_0 (+ pat$1 (* 513 0) (* 256 1) 0))
                                  (q.0$1_0 _$1_49)
                                  (_$2_38 (distinct k.0$2_0_old 0)))
                                 (=>
                                    _$2_38
                                    (let
                                       ((_$2_39 k.0$2_0_old))
                                       (let
                                          ((_$2_40 (+ s.1$2_0_old _$2_39)))
                                          (let
                                             ((_$2_41 (select HEAP$2_old _$2_40)))
                                             (let
                                                ((_$2_42 _$2_41))
                                                (let
                                                   ((_$2_43 (+ (+ pat$2 (* 513 0) (* 256 2) 0) _$2_42)))
                                                   (let
                                                      ((_$2_44 (select HEAP$2_old _$2_43)))
                                                      (let
                                                         ((_$2_45 _$2_44))
                                                         (let
                                                            ((s.1$2_0 _$2_40)
                                                             (k.0$2_0 _$2_45))
                                                            false))))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (p.0$1_0_old Int)
       (q.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (p.0$2_0_old Int)
       (q.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_13_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old p.0$1_0_old q.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old p.0$2_0_old q.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_51 (< p.0$1_0_old _$1_25_old)))
            (=>
               _$1_51
               (let
                  ((_$1_55 (+ q.0$1_0_old 1))
                   (_$1_56 (select HEAP$1_old q.0$1_0_old)))
                  (let
                     ((_$1_57 _$1_56)
                      (_$1_58 (+ p.0$1_0_old 1))
                      (_$1_59 (select HEAP$1_old p.0$1_0_old)))
                     (let
                        ((_$1_60 _$1_59))
                        (let
                           ((_$1_61 (distinct _$1_57 _$1_60)))
                           (=>
                              _$1_61
                              (let
                                 ((nmatch.1$1_0 nmatch.0$1_0_old)
                                  (_$1_63 (+ s.1$1_0_old 1)))
                                 (let
                                    ((s.0$1_0 _$1_63)
                                     (nmatch.0$1_0 nmatch.1$1_0)
                                     (_$2_51 (< p.0$2_0_old _$2_25_old)))
                                    (=>
                                       _$2_51
                                       (let
                                          ((_$2_55 (+ q.0$2_0_old 1))
                                           (_$2_56 (select HEAP$2_old q.0$2_0_old)))
                                          (let
                                             ((_$2_57 _$2_56)
                                              (_$2_58 (+ p.0$2_0_old 1))
                                              (_$2_59 (select HEAP$2_old p.0$2_0_old)))
                                             (let
                                                ((_$2_60 _$2_59))
                                                (let
                                                   ((_$2_61 (distinct _$2_57 _$2_60)))
                                                   (=>
                                                      (not _$2_61)
                                                      (let
                                                         ((p.0$2_0 _$2_58)
                                                          (q.0$2_0 _$2_55))
                                                         false)))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (p.0$1_0_old Int)
       (q.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (p.0$2_0_old Int)
       (q.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_13_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old p.0$1_0_old q.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old p.0$2_0_old q.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_51 (< p.0$1_0_old _$1_25_old)))
            (=>
               (not _$1_51)
               (let
                  ((_$1_62 (+ nmatch.0$1_0_old 1)))
                  (let
                     ((nmatch.1$1_0 _$1_62)
                      (_$1_63 (+ s.1$1_0_old 1)))
                     (let
                        ((s.0$1_0 _$1_63)
                         (nmatch.0$1_0 nmatch.1$1_0)
                         (_$2_51 (< p.0$2_0_old _$2_25_old)))
                        (=>
                           _$2_51
                           (let
                              ((_$2_55 (+ q.0$2_0_old 1))
                               (_$2_56 (select HEAP$2_old q.0$2_0_old)))
                              (let
                                 ((_$2_57 _$2_56)
                                  (_$2_58 (+ p.0$2_0_old 1))
                                  (_$2_59 (select HEAP$2_old p.0$2_0_old)))
                                 (let
                                    ((_$2_60 _$2_59))
                                    (let
                                       ((_$2_61 (distinct _$2_57 _$2_60)))
                                       (=>
                                          (not _$2_61)
                                          (let
                                             ((p.0$2_0 _$2_58)
                                              (q.0$2_0 _$2_55))
                                             false)))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (p.0$1_0_old Int)
       (q.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (p.0$2_0_old Int)
       (q.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_13_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old p.0$1_0_old q.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old p.0$2_0_old q.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_51 (< p.0$1_0_old _$1_25_old)))
            (=>
               _$1_51
               (let
                  ((_$1_55 (+ q.0$1_0_old 1))
                   (_$1_56 (select HEAP$1_old q.0$1_0_old)))
                  (let
                     ((_$1_57 _$1_56)
                      (_$1_58 (+ p.0$1_0_old 1))
                      (_$1_59 (select HEAP$1_old p.0$1_0_old)))
                     (let
                        ((_$1_60 _$1_59))
                        (let
                           ((_$1_61 (distinct _$1_57 _$1_60)))
                           (=>
                              (not _$1_61)
                              (let
                                 ((p.0$1_0 _$1_58)
                                  (q.0$1_0 _$1_55)
                                  (_$2_51 (< p.0$2_0_old _$2_25_old)))
                                 (=>
                                    _$2_51
                                    (let
                                       ((_$2_55 (+ q.0$2_0_old 1))
                                        (_$2_56 (select HEAP$2_old q.0$2_0_old)))
                                       (let
                                          ((_$2_57 _$2_56)
                                           (_$2_58 (+ p.0$2_0_old 1))
                                           (_$2_59 (select HEAP$2_old p.0$2_0_old)))
                                          (let
                                             ((_$2_60 _$2_59))
                                             (let
                                                ((_$2_61 (distinct _$2_57 _$2_60)))
                                                (=>
                                                   _$2_61
                                                   (let
                                                      ((nmatch.1$2_0 nmatch.0$2_0_old)
                                                       (_$2_63 (+ s.1$2_0_old 1)))
                                                      (let
                                                         ((s.0$2_0 _$2_63)
                                                          (nmatch.0$2_0 nmatch.1$2_0))
                                                         false)))))))))))))))))))
(assert
   (forall
      ((_$1_1_old Int)
       (_$1_25_old Int)
       (_$1_7_old Int)
       (nmatch.0$1_0_old Int)
       (p.0$1_0_old Int)
       (q.0$1_0_old Int)
       (s.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (_$2_1_old Int)
       (_$2_25_old Int)
       (_$2_7_old Int)
       (nmatch.0$2_0_old Int)
       (p.0$2_0_old Int)
       (q.0$2_0_old Int)
       (s.1$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_13_MAIN _$1_1_old _$1_25_old _$1_7_old nmatch.0$1_0_old p.0$1_0_old q.0$1_0_old s.1$1_0_old i1 (select HEAP$1_old i1) _$2_1_old _$2_25_old _$2_7_old nmatch.0$2_0_old p.0$2_0_old q.0$2_0_old s.1$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_51 (< p.0$1_0_old _$1_25_old)))
            (=>
               _$1_51
               (let
                  ((_$1_55 (+ q.0$1_0_old 1))
                   (_$1_56 (select HEAP$1_old q.0$1_0_old)))
                  (let
                     ((_$1_57 _$1_56)
                      (_$1_58 (+ p.0$1_0_old 1))
                      (_$1_59 (select HEAP$1_old p.0$1_0_old)))
                     (let
                        ((_$1_60 _$1_59))
                        (let
                           ((_$1_61 (distinct _$1_57 _$1_60)))
                           (=>
                              (not _$1_61)
                              (let
                                 ((p.0$1_0 _$1_58)
                                  (q.0$1_0 _$1_55)
                                  (_$2_51 (< p.0$2_0_old _$2_25_old)))
                                 (=>
                                    (not _$2_51)
                                    (let
                                       ((_$2_62 (+ nmatch.0$2_0_old 1)))
                                       (let
                                          ((nmatch.1$2_0 _$2_62)
                                           (_$2_63 (+ s.1$2_0_old 1)))
                                          (let
                                             ((s.0$2_0 _$2_63)
                                              (nmatch.0$2_0 nmatch.1$2_0))
                                             false)))))))))))))))
; end
(check-sat)
(get-model)
