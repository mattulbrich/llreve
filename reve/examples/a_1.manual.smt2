; Manual translation to smt
; This is the 1-program-problem of proving a contract correct - not yet the relational one.

; Contract pre: 1=1, post: \result >= 0

(declare-fun INV (Int Int Int) Bool)

;(define-fun INV ((n Int)(i Int)(s Int)) Bool
;  (and (>= i 2) (>= s 0)))

; Starting in the beginning and reaching the mark
(assert
 (forall ((n Int))
  (let ((i0 2))
  (let ((sum0 0))
  (let ((v2 (<= i0 n)))
  (=>
   (and
    (= 1 1) ; precondition
    v2) ; path condition
   (INV n i0 sum0)))))))

; Starting in the beginning and reaching the end
(assert
 (forall ((n Int))
  (let ((i0 2))
  (let ((sum0 0))
  (let ((v2 (<= i0 n)))
  (=>
   (and
    (= 1 1)
    (not v2))
   (>= sum0 0)))))))

; Starting at the mark and reaching the mark
(assert
 (forall ((sum0 Int)(i0 Int)(n Int))
  (let ((v4 (+ sum0 i0)))
  (let ((v6 (+ i0 1)))
  (let ((i0$ v6))
  (let ((sum0$ v4))
  (let ((v2 (<= i0$ n)))
  (=>
   (and
    (INV n i0 sum0)
    v2)
   (INV n i0$ sum0$)))))))))

; Starting at the mark and reaching the end of the program
(assert
 (forall ((sum0 Int)(i0 Int)(n Int))
  (let ((v4 (+ sum0 i0)))
  (let ((v6 (+ i0 1)))
  (let ((i0$ v6))
  (let ((sum0$ v4))
  (let ((v2 (<= i0$ n)))
  (=>
   (and
    (INV n i0 sum0)
    (not v2))
   (>= sum0$ 0)))))))))

(check-sat)
