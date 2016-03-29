(set-info :origin "NTS benchmark converted to SMT-LIB2 using Eldarica (http://lara.epfl.ch/w/eldarica)")
(set-logic HORN)
(declare-fun INV_MAIN_0 (Int Int Int Int) Bool)
;; (define-fun INV_MAIN_0 ((A Int) (B Int) (C Int) (D Int)) Bool (and (and (= A C) (= B D)) (>= A 0)))
(assert
 (forall ((i$1 Int) (n$1 Int) (i$2 Int) (n$2 Int))
         (=> (and (= i$1 0) (= i$2 0) (= n$1 n$2))
             (INV_MAIN_0 i$1 n$1 i$2 n$2))))
(assert
 (forall ((i$2 Int) (i$1 Int) (n$2 Int) (n$1 Int))
         (=> (and
               (= i$1 1)
               (not (< i$2 n$2))
               (not (< i$1 n$1))
               (INV_MAIN_0 i$1 n$1 i$2 n$2))
             (= i$2 1))))
(assert
 (forall ((n$1 Int) (n$2 Int) (i$1 Int) (i$2 Int))
         (=> (and (< i$1 n$1)
                  (< i$2 n$2)
                  (INV_MAIN_0 i$1 n$1 i$2 n$2))
             (INV_MAIN_0 (+ i$1 1) n$1 (+ i$2 1) n$2))))
(assert
 (forall ((n$2 Int) (i$2 Int) (n$1 Int) (i$1 Int))
         (=>
          (and (>= (+ (- n$2 i$2) (- 1)) 0)
               (not (>= (+ (- n$1 i$1) (- 1)) 0))
               (INV_MAIN_0 i$1 n$1 i$2 n$2))
          false)))
(assert
 (forall ((n$2 Int) (i$2 Int) (n$1 Int) (i$1 Int))
         (=> (and (not (>= (+ (- n$2 i$2) (- 1)) 0))
                  (>= (+ (- n$1 i$1) (- 1)) 0)
                  (INV_MAIN_0 i$1 n$1 i$2 n$2))
             false)))
(check-sat)
