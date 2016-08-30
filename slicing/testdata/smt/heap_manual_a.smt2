(set-logic HORN)
(assert
   (forall
      ((HEAP$1 (Array Int Int)))
      (let
         ((HEAP$1_mod (store HEAP$1 20 6)))
         (let
            ((res$1 (select HEAP$1_mod 20))
             (res$2 (select HEAP$1 20)))
            (= res$1 res$2)))))
(check-sat)
(get-model)
