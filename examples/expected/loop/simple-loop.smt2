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
    Int)
   Bool)
(declare-fun
   INV_42_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_42__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_42__2
   (Int
    Int)
   Bool)
(assert
   (forall
      ((z$1_0 Int)
       (z$2_0 Int)
       (result$1 Int)
       (result$2 Int))
      (=>
         (and
            (= z$1_0 z$2_0))
         (and
            (=>
               (INV_REC_f z$1_0 z$2_0 result$1 result$2)
               (= result$1 result$2))
            (INV_REC_f_PRE z$1_0 z$2_0)))))
(assert
   (forall
      ((z$1_0_old Int)
       (z$2_0_old Int))
      (=>
         (INV_REC_f_PRE z$1_0_old z$2_0_old)
         (let
            ((i.0$1_0 0)
             (i.0$2_0 1))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_42_PRE i.0$1_0 i.0$2_0)
                  (=>
                     (INV_42 i.0$1_0 i.0$2_0 result$1 result$2)
                     (INV_REC_f z$1_0_old z$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old i.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 i.0$1_0_old)
                   (_$2_1 (<= i.0$2_0_old 10)))
                  (=>
                     (not _$2_1)
                     (let
                        ((result$2 i.0$2_0_old))
                        (INV_42 i.0$1_0_old i.0$2_0_old result$1 result$2)))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old i.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_5)
                      (_$2_1 (<= i.0$2_0_old 10)))
                     (=>
                        _$2_1
                        (let
                           ((_$2_5 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_5))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_42_PRE i.0$1_0 i.0$2_0)
                                    (=>
                                       (INV_42 i.0$1_0 i.0$2_0 result$1 result$2)
                                       (INV_42 i.0$1_0_old i.0$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((z$1_0_old Int))
      (let
         ((i.0$1_0 0))
         (forall
            ((result$1 Int))
            (=>
               (INV_42__1 i.0$1_0 result$1)
               (INV_REC_f__1 z$1_0_old result$1))))))
(assert
   (forall
      ((i.0$1_0_old Int))
      (let
         ((_$1_1 (<= i.0$1_0_old 10)))
         (=>
            (not _$1_1)
            (let
               ((result$1 i.0$1_0_old))
               (INV_42__1 i.0$1_0_old result$1))))))
(assert
   (forall
      ((i.0$1_0_old Int))
      (let
         ((_$1_1 (<= i.0$1_0_old 10)))
         (=>
            _$1_1
            (let
               ((_$1_5 (+ i.0$1_0_old 1)))
               (let
                  ((i.0$1_0 _$1_5))
                  (forall
                     ((result$1 Int))
                     (=>
                        (INV_42__1 i.0$1_0 result$1)
                        (INV_42__1 i.0$1_0_old result$1)))))))))
(assert
   (forall
      ((z$2_0_old Int))
      (let
         ((i.0$2_0 1))
         (forall
            ((result$2 Int))
            (=>
               (INV_42__2 i.0$2_0 result$2)
               (INV_REC_f__2 z$2_0_old result$2))))))
(assert
   (forall
      ((i.0$2_0_old Int))
      (let
         ((_$2_1 (<= i.0$2_0_old 10)))
         (=>
            (not _$2_1)
            (let
               ((result$2 i.0$2_0_old))
               (INV_42__2 i.0$2_0_old result$2))))))
(assert
   (forall
      ((i.0$2_0_old Int))
      (let
         ((_$2_1 (<= i.0$2_0_old 10)))
         (=>
            _$2_1
            (let
               ((_$2_5 (+ i.0$2_0_old 1)))
               (let
                  ((i.0$2_0 _$2_5))
                  (forall
                     ((result$2 Int))
                     (=>
                        (INV_42__2 i.0$2_0 result$2)
                        (INV_42__2 i.0$2_0_old result$2)))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((i.0$1_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old i.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old 10)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_5))
                     (=>
                        (and
                           (let
                              ((_$2_1 (<= i.0$2_0_old 10)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_5 (+ i.0$2_0_old 1)))
                                    (let
                                       ((i.0$2_0 _$2_5))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_42_PRE i.0$1_0 i.0$2_0_old)
                              (=>
                                 (INV_42 i.0$1_0 i.0$2_0_old result$1 result$2)
                                 (INV_42 i.0$1_0_old i.0$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (i.0$2_0_old Int))
      (=>
         (INV_42_PRE i.0$1_0_old i.0$2_0_old)
         (let
            ((_$2_1 (<= i.0$2_0_old 10)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ i.0$2_0_old 1)))
                  (let
                     ((i.0$2_0 _$2_5))
                     (=>
                        (and
                           (let
                              ((_$1_1 (<= i.0$1_0_old 10)))
                              (=>
                                 _$1_1
                                 (let
                                    ((_$1_5 (+ i.0$1_0_old 1)))
                                    (let
                                       ((i.0$1_0 _$1_5))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_42_PRE i.0$1_0_old i.0$2_0)
                              (=>
                                 (INV_42 i.0$1_0_old i.0$2_0 result$1 result$2)
                                 (INV_42 i.0$1_0_old i.0$2_0_old result$1 result$2))))))))))))
(check-sat)
(get-model)
