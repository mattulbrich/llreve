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
(declare-fun
   INV_1_MAIN
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_2_MAIN
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            n$1_0_old
            n$2_0_old)
         (let
            ((n$1_0 n$1_0_old)
             (i.0$1_0 1)
             (x.0$1_0 1)
             (n$2_0 n$2_0_old)
             (i.0$2_0 1)
             (x.0$2_0 1))
            (INV_1_MAIN i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)))))
(assert
 (forall
  ((i.0$1_0_old Int)
   (n$1_0_old Int)
   (x.0$1_0_old Int)
   (i.0$2_0_old Int)
   (n$2_0_old Int)
   (x.0$2_0_old Int))
  (=>
   (and
    (<= i.0$1_0_old n$1_0_old)
    (<= i.0$2_0_old n$2_0_old)
    (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old))
   (let
       ((i.0$1_0 (+ i.0$1_0_old 1))
        (x.0$1_0 (* x.0$1_0_old 5))
        (i.0$2_0 (+ i.0$2_0_old 1))
        (x.0$2_0 (* x.0$2_0_old 5)))
     (INV_1_MAIN i.0$1_0 n$1_0_old x.0$1_0 i.0$2_0 n$2_0_old x.0$2_0)))))
(assert
 (forall
  ((i.0$1_0_old Int)
   (n$1_0_old Int)
   (x.0$1_0_old Int)
   (i.0$2_0_old Int)
   (n$2_0_old Int)
   (x.0$2_0_old Int))
  (=>
   (and
    (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
    (<= i.0$1_0_old n$1_0_old)
    (not (<= i.0$2_0_old n$2_0_old)))
   (let
       ((i.0$1_0 (+ i.0$1_0_old 1))
        (x.0$1_0 (* x.0$1_0_old 5)))
     (INV_1_MAIN i.0$1_0 n$1_0_old x.0$1_0 i.0$2_0_old n$2_0_old x.0$2_0_old)))))
(assert
 (forall
  ((i.0$1_0_old Int)
   (n$1_0_old Int)
   (x.0$1_0_old Int)
   (i.0$2_0_old Int)
   (n$2_0_old Int)
   (x.0$2_0_old Int))
  (=>
   (and
    (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
    (<= i.0$2_0_old n$2_0_old)
    (not (<= i.0$1_0_old n$1_0_old)))
   (let
       ((i.0$2_0 (+ i.0$2_0_old 1))
        (x.0$2_0 (* x.0$2_0_old 5)))
     (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0 n$2_0_old x.0$2_0)))))
(assert
 (forall
  ((i.0$1_0_old Int)
   (n$1_0_old Int)
   (x.0$1_0_old Int)
   (i.0$2_0_old Int)
   (n$2_0_old Int)
   (x.0$2_0_old Int))
  (=>
   (and
    (INV_1_MAIN i.0$1_0_old n$1_0_old x.0$1_0_old i.0$2_0_old n$2_0_old x.0$2_0_old)
    (not (<= i.0$1_0_old n$1_0_old))
    (not (<= i.0$2_0_old n$2_0_old)))
   (let
       ((i.1$1_0 0)
        (i.1$2_0 1))
     (and
      (INV_2_MAIN i.1$1_0 n$1_0_old x.0$1_0_old i.1$2_0 n$2_0_old x.0$2_0_old)
      )))))
(assert
   (forall
      ((i.1$1_0_old Int)
       (n$1_0_old Int)
       (x.1$1_0_old Int)
       (i.1$2_0_old Int)
       (n$2_0_old Int)
       (x.1$2_0_old Int))
      (=>
       (and
        (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
        (not (<= i.1$1_0_old n$1_0_old))
        (not (<= i.1$2_0_old n$2_0_old)))
       (let
           ((result$1 x.1$1_0_old)
            (result$2 x.1$2_0_old))
         (OUT_INV
          result$1
          result$2)))))
(assert
 (forall
  ((i.1$1_0_old Int)
   (n$1_0_old Int)
   (x.1$1_0_old Int)
   (i.1$2_0_old Int)
   (n$2_0_old Int)
   (x.1$2_0_old Int))
  (=>
   (and
    (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
    (<= i.1$1_0_old n$1_0_old)
    (<= i.1$2_0_old n$2_0_old))
   (let
       ((i.1$1_0 (+ i.1$1_0_old 1))
        (x.1$1_0 (+ x.1$1_0_old i.1$1_0_old))
        (i.1$2_0 (+ i.1$2_0_old 1))
        (x.1$2_0 (+ x.1$2_0_old i.1$2_0_old)))
     (INV_2_MAIN i.1$1_0 n$1_0_old x.1$1_0 i.1$2_0 n$2_0_old x.1$2_0)))))
(assert
 (forall
  ((i.1$1_0_old Int)
   (n$1_0_old Int)
   (x.1$1_0_old Int)
   (i.1$2_0_old Int)
   (n$2_0_old Int)
   (x.1$2_0_old Int))
  (=>
   (and
    (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
    (<= i.1$1_0_old n$1_0_old)
    (not (<= i.1$2_0_old n$2_0_old)))
   (let
       ((i.1$1_0 (+ i.1$1_0_old 1))
        (x.1$1_0 (+ x.1$1_0_old i.1$1_0_old)))
     (INV_2_MAIN i.1$1_0 n$1_0_old x.1$1_0 i.1$2_0_old n$2_0_old x.1$2_0_old)))))
(assert
 (forall
  ((i.1$1_0_old Int)
   (n$1_0_old Int)
   (x.1$1_0_old Int)
   (i.1$2_0_old Int)
   (n$2_0_old Int)
   (x.1$2_0_old Int))
  (=>
   (and
    (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0_old n$2_0_old x.1$2_0_old)
    (<= i.1$2_0_old n$2_0_old)
    (not (<= i.1$1_0_old n$1_0_old)))
   (let
       ((i.1$2_0 (+ i.1$2_0_old 1))
        (x.1$2_0 (+ x.1$2_0_old i.1$2_0_old)))
     (INV_2_MAIN i.1$1_0_old n$1_0_old x.1$1_0_old i.1$2_0 n$2_0_old x.1$2_0)))))
; end
(check-sat)
(get-model)
