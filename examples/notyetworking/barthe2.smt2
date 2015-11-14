(set-logic HORN)
(declare-fun
   INV_REC
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_PRE
   (Int
    Int)
   Bool)
(define-fun
   INV_1
   ((i1 Int)
    (j2 Int)
    (n1 Int)
    (n2 Int)
    (x1 Int)
    (x2 Int)
    (res1 Int)
    (res2 Int))
   Bool
   (or
    (and (= (+ i1 1) j2) (<= i1 n1) (<= j2 n2) (= (+ x1 i1) x2) (= res1 res2) (= n1 n2))
    (and (= i1 0) (= j2 1) (= x1 x2) (= res1 res2) (= n1 n2))
    (and (= j2 (+ n2 1)) (= i1 n1) (= (+ x1 i1) x2) (= res1 res2) (= n1 n2))
    (and (= j2 i1) (= n1 n2) (= res1 res2) (= x1 x2) (= i1 (+ 1 n1)))))
(declare-fun
   INV_1_PRE
   (Int
    Int
    Int
    Int
    Int
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
               (INV_REC n$1_0 n$2_0 result$1 result$2)
               (= result$1 result$2))
            (INV_REC_PRE n$1_0 n$2_0)))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_PRE n$1_0_old n$2_0_old)
         (let
            ((i.0$1_0 0)
             (x.0$1_0 0)
             (n$1_0 n$1_0_old)
             (j.0$2_0 1)
             (x.0$2_0 0)
             (n$2_0 n$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_1_PRE i.0$1_0 j.0$2_0 n$1_0 n$2_0 x.0$1_0 x.0$2_0)
                  (=>
                     (INV_1 i.0$1_0 j.0$2_0 n$1_0 n$2_0 x.0$1_0 x.0$2_0 result$1 result$2)
                     (INV_REC n$1_0_old n$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$2_0_old Int)
       (n$1_0_old Int)
       (n$2_0_old Int)
       (x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_PRE i.0$1_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 x.0$1_0_old)
                   (_$2_1 (<= j.0$2_0_old n$2_0_old)))
                  (=>
                     (not _$2_1)
                     (let
                        ((result$2 x.0$2_0_old))
                        (INV_1 i.0$1_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old result$1 result$2)))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$2_0_old Int)
       (n$1_0_old Int)
       (n$2_0_old Int)
       (x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_PRE i.0$1_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ x.0$1_0_old i.0$1_0_old))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (x.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old)
                      (_$2_1 (<= j.0$2_0_old n$2_0_old)))
                     (=>
                        _$2_1
                        (let
                           ((_$2_5 (+ x.0$2_0_old j.0$2_0_old))
                            (_$2_6 (+ j.0$2_0_old 1)))
                           (let
                              ((j.0$2_0 _$2_6)
                               (x.0$2_0 _$2_5)
                               (n$2_0 n$2_0_old))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_1_PRE i.0$1_0 j.0$2_0 n$1_0 n$2_0 x.0$1_0 x.0$2_0)
                                    (=>
                                       (INV_1 i.0$1_0 j.0$2_0 n$1_0 n$2_0 x.0$1_0 x.0$2_0 result$1 result$2)
                                       (INV_1 i.0$1_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old result$1 result$2))))))))))))))
; OFF BY N
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$2_0_old Int)
       (n$1_0_old Int)
       (n$2_0_old Int)
       (x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_PRE i.0$1_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old)
         (let
            ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ x.0$1_0_old i.0$1_0_old))
                   (_$1_6 (+ i.0$1_0_old 1)))
                  (let
                     ((i.0$1_0 _$1_6)
                      (x.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_1 (<= j.0$2_0_old n$2_0_old)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_5 (+ x.0$2_0_old j.0$2_0_old))
                                     (_$2_6 (+ j.0$2_0_old 1)))
                                    (let
                                       ((j.0$2_0 _$2_6)
                                        (x.0$2_0 _$2_5)
                                        (n$2_0 n$2_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_1_PRE i.0$1_0 j.0$2_0_old n$1_0 n$2_0_old x.0$1_0 x.0$2_0_old)
                              (=>
                                 (INV_1 i.0$1_0 j.0$2_0_old n$1_0 n$2_0_old x.0$1_0 x.0$2_0_old result$1 result$2)
                                 (INV_1 i.0$1_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((i.0$1_0_old Int)
       (j.0$2_0_old Int)
       (n$1_0_old Int)
       (n$2_0_old Int)
       (x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (=>
         (INV_1_PRE i.0$1_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old)
         (let
            ((_$2_1 (<= j.0$2_0_old n$2_0_old)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ x.0$2_0_old j.0$2_0_old))
                   (_$2_6 (+ j.0$2_0_old 1)))
                  (let
                     ((j.0$2_0 _$2_6)
                      (x.0$2_0 _$2_5)
                      (n$2_0 n$2_0_old))
                     (=>
                        (and
                           (let
                              ((_$1_1 (<= i.0$1_0_old n$1_0_old)))
                              (=>
                                 _$1_1
                                 (let
                                    ((_$1_5 (+ x.0$1_0_old i.0$1_0_old))
                                     (_$1_6 (+ i.0$1_0_old 1)))
                                    (let
                                       ((i.0$1_0 _$1_6)
                                        (x.0$1_0 _$1_5)
                                        (n$1_0 n$1_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_1_PRE i.0$1_0_old j.0$2_0 n$1_0_old n$2_0 x.0$1_0_old x.0$2_0)
                              (=>
                                 (INV_1 i.0$1_0_old j.0$2_0 n$1_0_old n$2_0 x.0$1_0_old x.0$2_0 result$1 result$2)
                                 (INV_1 i.0$1_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old result$1 result$2))))))))))))
(check-sat)
(get-model)
