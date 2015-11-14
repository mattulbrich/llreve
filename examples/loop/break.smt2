(set-logic HORN)
(declare-fun INV_0 (Int Int Int) Bool)
(assert
 (forall ((x Int))
         (INV_0 x 0 10)))
(assert
 (forall ((x Int) (i.0$1_0 Int) (i.0$2_0 Int))
         (=> (INV_0 x i.0$1_0 i.0$2_0)
             (let ((_$1_0 (<= i.0$1_0 10))
                   (_$2_0 (>= i.0$2_0 0)))
               (=>
                (and (not _$1_0) (not _$2_0))
                (let ((_$2_4 (- 10 i.0$2_0)))
                  (let ((result$2 _$2_4)
                        (result$1 i.0$1_0))
                    (= result$1 result$2))))))))
(assert
 (forall ((x Int) (i.0$1_0 Int) (i.0$2_0 Int))
         (=> (INV_0 x i.0$1_0 i.0$2_0)
             (let ((_$1_0 (<= i.0$1_0 10))
                   (_$2_0 (>= i.0$2_0 0)))
               (=>
                (and _$1_0 _$2_0)
                (let ((_$1_1 (= i.0$1_0 x))
                      (_$2_1 (- 10 x)))
                  (let
                      ((_$2_2 (= i.0$2_0 _$2_1)))
                    (=>
                     (and _$1_1 _$2_2)
                     (let ((_$2_4 (- 10 i.0$2_0)))
                       (let ((result$2 _$2_4)
                             (result$1 i.0$1_0))
                         (= result$1 result$2)))))))))))
(assert
 (forall ((x Int) (i.0$1_0 Int) (i.0$2_0 Int))
         (=> (INV_0 x i.0$1_0 i.0$2_0)
             (let ((_$1_0 (<= i.0$1_0 10))
                   (_$2_0 (>= i.0$2_0 0)))
               (=>
                (and _$1_0 _$2_0)
                (let ((_$1_1 (= i.0$1_0 x))
                      (_$2_1 (- 10 x)))
                  (let
                      ((_$2_2 (= i.0$2_0 _$2_1)))
                    (=>
                     (and (not _$1_1) (not _$2_2))
                     (let ((_$1_2 (+ i.0$1_0 1))
                           (_$2_3 (- i.0$2_0 1)))
                       (INV_0 x _$1_2 _$2_3))))))))))
(check-sat)
(get-model)
