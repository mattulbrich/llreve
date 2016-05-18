(set-logic HORN)
(define-fun
   IN_INV
   ((n$1_0 Int)
    (n$2_0 Int))
   Bool
   (and
    (>= n$1_0 1)
    (>= n$2_0 1)
      (= n$1_0 n$2_0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(define-fun
   INV_MAIN_1
   ((i.0$1_0 Int)
    (n$1_0 Int)
    (res.0$1_0 Int)
    (i.0$2_0 Int)
    (res.0$2_0 Int))
   Bool
   (or (or
      false
      false
      (= (+ i.0$1_0 i.0$2_0) (+ n$1_0 1))
      (= (* (- i.0$1_0 1) i.0$1_0) (* 2 res.0$1_0))
      (= (- (* n$1_0 (+ n$1_0 1)) (* i.0$2_0 (+ i.0$2_0 1))) (* 2 res.0$2_0))
      ;; (>= i.0$1_0 1)
      ;; (<= i.0$1_0 (+ n$1_0 1))
      ;; (>= i.0$2_0 0)
      ;; (<= i.0$2_0 n$1_0)
      )))
(assert
   (forall
      ((n$1_0 Int)
       (n$2_0 Int))
      (=>
         (IN_INV n$1_0 n$2_0)
         (INV_MAIN_1 1 n$1_0 0 n$1_0 0))))
(assert
 (forall
  ((i.0$1_0 Int)
   (n$1_0 Int)
   (res.0$1_0 Int)
   (i.0$2_0 Int)
   (res.0$2_0 Int))
  (=>
   (and
    (INV_MAIN_1 i.0$1_0 n$1_0 res.0$1_0 i.0$2_0 res.0$2_0)
    (not (<= i.0$1_0 n$1_0))
    (not (>= i.0$2_0 1)))
   (OUT_INV res.0$1_0 res.0$2_0))))
(assert
 (forall
  ((i.0$1_0 Int)
   (n$1_0 Int)
   (res.0$1_0 Int)
   (i.0$2_0 Int)
   (res.0$2_0 Int))
  (=>
   (and
    (INV_MAIN_1 i.0$1_0 n$1_0 res.0$1_0 i.0$2_0 res.0$2_0)
    (<= i.0$1_0 n$1_0)
    (>= i.0$2_0 1))
   (INV_MAIN_1 (+ i.0$1_0 1) n$1_0 (+ res.0$1_0 i.0$1_0) (- i.0$2_0 1) (+ res.0$2_0 i.0$2_0)))))
(assert
   (forall
      ((i.0$1_0 Int)
       (n$1_0 Int)
       (res.0$1_0 Int)
       (i.0$2_0 Int)
       (res.0$2_0 Int))
      (=>
       (and
        (INV_MAIN_1 i.0$1_0 n$1_0 res.0$1_0 i.0$2_0 res.0$2_0)
        (not (<= i.0$1_0 n$1_0))
        (>= i.0$2_0 1))
       false)))
(assert
   (forall
      ((i.0$1_0 Int)
       (n$1_0 Int)
       (res.0$1_0 Int)
       (i.0$2_0 Int)
       (res.0$2_0 Int))
      (=>
       (and
        (INV_MAIN_1 i.0$1_0 n$1_0 res.0$1_0 i.0$2_0 res.0$2_0)
        (<= i.0$1_0 n$1_0)
        (not (>= i.0$2_0 1)))
       false)))
(check-sat)
(get-model)
