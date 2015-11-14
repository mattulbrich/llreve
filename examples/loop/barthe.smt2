(set-logic HORN)
(declare-fun
   INV_REC
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(define-fun
   INV_42
   ((c1 Int)
    (i1 Int)
    (i2 Int)
    (j2 Int)
    (n1 Int)
    (n2 Int)
    (x1 Int)
    (x2 Int)
    (res1 Int)
    (res2 Int))
   Bool
   (=> (and (= x1 x2) (= i1 i2) (= n1 n2) (= (- j2 c1) (* 5 i1))) (= res1 res2)))
(assert
   (forall
      ((c$1_0 Int)
       (c$2_0 Int)
       (n$1_0 Int)
       (n$2_0 Int)
       (result$1 Int)
       (result$2 Int))
      (=>
         (and
            (= c$1_0 c$2_0)
            (= n$1_0 n$2_0))
         (=>
            (INV_REC c$1_0 c$2_0 n$1_0 n$2_0 result$1 result$2)
            (= result$1 result$2)))))
(assert
   (forall
      ((c$1_0_old Int)
       (c$2_0_old Int)
       (n$1_0_old Int)
       (n$2_0_old Int))
      (let
         ((i.0$1_0 0))
         (let
            ((x.0$1_0 0)
             (_$1_0 (< i.0$1_0 n$1_0_old)))
            (=>
               (not _$1_0)
               (let
                  ((result$1 x.0$1_0)
                   (i.0$2_0 0))
                  (let
                     ((j.0$2_0 c$2_0_old)
                      (x.0$2_0 0)
                      (_$2_0 (< i.0$2_0 n$2_0_old)))
                     (=>
                        (not _$2_0)
                        (let
                           ((result$2 x.0$2_0))
                           (INV_REC c$1_0_old c$2_0_old n$1_0_old n$2_0_old result$1 result$2))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (c$2_0_old Int)
       (n$1_0_old Int)
       (n$2_0_old Int))
      (let
         ((i.0$1_0 0))
         (let
            ((x.0$1_0 0)
             (_$1_0 (< i.0$1_0 n$1_0_old)))
            (=>
               _$1_0
               (let
                  ((c$1_0 c$1_0_old)
                   (n$1_0 n$1_0_old)
                   (i.0$2_0 0))
                  (let
                     ((j.0$2_0 c$2_0_old)
                      (x.0$2_0 0)
                      (_$2_0 (< i.0$2_0 n$2_0_old)))
                     (=>
                        _$2_0
                        (let
                           ((n$2_0 n$2_0_old))
                           (forall
                              ((result$1 Int)
                               (result$2 Int))
                              (=>
                                 (INV_42 c$1_0 i.0$1_0 i.0$2_0 j.0$2_0 n$1_0 n$2_0 x.0$1_0 x.0$2_0 result$1 result$2)
                                 (INV_REC c$1_0_old c$2_0_old n$1_0_old n$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (i.0$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$1_0_old Int)
       (n$2_0_old Int)
       (x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (let
         ((_$1_1 (* 5 i.0$1_0_old)))
         (let
            ((_$1_2 (+ _$1_1 c$1_0_old)))
            (let
               ((_$1_3 (+ x.0$1_0_old _$1_2))
                (_$1_4 (+ i.0$1_0_old 1)))
               (let
                  ((i.0$1_0 _$1_4))
                  (let
                     ((x.0$1_0 _$1_3)
                      (_$1_0 (< i.0$1_0 n$1_0_old)))
                     (=>
                        (not _$1_0)
                        (let
                           ((result$1 x.0$1_0)
                            (_$2_2 (+ x.0$2_0_old j.0$2_0_old))
                            (_$2_3 (+ j.0$2_0_old 5))
                            (_$2_4 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_4))
                              (let
                                 ((j.0$2_0 _$2_3)
                                  (x.0$2_0 _$2_2)
                                  (_$2_0 (< i.0$2_0 n$2_0_old)))
                                 (=>
                                    (not _$2_0)
                                    (let
                                       ((result$2 x.0$2_0))
                                       (INV_42 c$1_0_old i.0$1_0_old i.0$2_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((c$1_0_old Int)
       (i.0$1_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (n$1_0_old Int)
       (n$2_0_old Int)
       (x.0$1_0_old Int)
       (x.0$2_0_old Int))
      (let
         ((_$1_1 (* 5 i.0$1_0_old)))
         (let
            ((_$1_2 (+ _$1_1 c$1_0_old)))
            (let
               ((_$1_3 (+ x.0$1_0_old _$1_2))
                (_$1_4 (+ i.0$1_0_old 1)))
               (let
                  ((i.0$1_0 _$1_4))
                  (let
                     ((x.0$1_0 _$1_3)
                      (_$1_0 (< i.0$1_0 n$1_0_old)))
                     (=>
                        _$1_0
                        (let
                           ((c$1_0 c$1_0_old)
                            (n$1_0 n$1_0_old)
                            (_$2_2 (+ x.0$2_0_old j.0$2_0_old))
                            (_$2_3 (+ j.0$2_0_old 5))
                            (_$2_4 (+ i.0$2_0_old 1)))
                           (let
                              ((i.0$2_0 _$2_4))
                              (let
                                 ((j.0$2_0 _$2_3)
                                  (x.0$2_0 _$2_2)
                                  (_$2_0 (< i.0$2_0 n$2_0_old)))
                                 (=>
                                    _$2_0
                                    (let
                                       ((n$2_0 n$2_0_old))
                                       (forall
                                          ((result$1 Int)
                                           (result$2 Int))
                                          (=>
                                             (INV_42 c$1_0 i.0$1_0 i.0$2_0 j.0$2_0 n$1_0 n$2_0 x.0$1_0 x.0$2_0 result$1 result$2)
                                             (INV_42 c$1_0_old i.0$1_0_old i.0$2_0_old j.0$2_0_old n$1_0_old n$2_0_old x.0$1_0_old x.0$2_0_old result$1 result$2))))))))))))))))
(check-sat)
(get-model)
