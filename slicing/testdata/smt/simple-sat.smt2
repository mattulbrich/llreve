(set-logic HORN)
(define-fun
   IN_INV
   ((a$1_0 Int)
    (a$2_0 Int))
   Bool
   (and
      (= a$1_0 a$2_0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(assert
   (forall
      ((a$1_0_old Int)
       (a$2_0_old Int))
      (=>
         (IN_INV a$1_0_old a$2_0_old)
         (let
            ((a$1_0 a$1_0_old))
            (let
               ((_$1_0 (+ a$1_0 0)))
               (let
                  ((result$1 _$1_0)
                   (a$2_0 a$2_0_old))
                  (let
                     ((result$2 a$2_0))
                     (OUT_INV result$1 result$2))))))))
(check-sat)
(get-model)
