(declare-rel
   INV_MAIN_1
   (Int
    Int
    Int
    Int
    Int
    Int))
(declare-rel
   INV_MAIN_2
   (Int
    Int
    Int
    Int
    Int
    Int))
(declare-rel
   INV_MAIN_3
   (Int
    Int
    Int
    Int
    Int
    Int))
(declare-var n$1_0 Int)
(declare-var n$2_0 Int)
(declare-var i.0$1_0 Int)
(declare-var i.1$1_0 Int)
(declare-var i.2$1_0 Int)
(declare-var x.0$1_0 Int)
(declare-var x.1$1_0 Int)
(declare-var x.2$1_0 Int)
(declare-var i.0$2_0 Int)
(declare-var i.1$2_0 Int)
(declare-var i.2$2_0 Int)
(declare-var x.0$2_0 Int)
(declare-var x.1$2_0 Int)
(declare-var x.2$2_0 Int)
(declare-rel END ())
(rule
 (=>
  (= n$1_0 n$2_0)
  (INV_MAIN_1 1 n$1_0 1 1 n$2_0 1)))
(rule
 (=> (and (INV_MAIN_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)
          (<= i.0$1_0 n$1_0)
          (<= i.0$2_0 n$2_0))
     (INV_MAIN_1 (+ i.0$1_0 1) n$1_0 (* x.0$1_0 1) (+ i.0$2_0 1) n$2_0 (* x.0$2_0 1))))
(rule
 (=>
  (and (INV_MAIN_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)
       (<= i.0$1_0 n$1_0)
       (not (<= i.0$2_0 n$2_0)))
  (INV_MAIN_1 (+ i.0$1_0 1) n$1_0 (* x.0$1_0 1) i.0$2_0 n$2_0 x.0$2_0)))
(rule
 (=>
  (and (INV_MAIN_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)
       (<= i.0$2_0 n$2_0)
       (not (<= i.0$1_0 n$1_0)))
  (INV_MAIN_1 i.0$1_0 n$1_0 x.0$1_0 (+ i.0$2_0 1) n$2_0 (* x.0$2_0 1))))
(rule
 (=>
  (and (INV_MAIN_1 i.0$1_0 n$1_0 x.0$1_0 i.0$2_0 n$2_0 x.0$2_0)
       (not (<= i.0$1_0 n$1_0))
       (not (<= i.0$2_0 n$2_0)))
  (INV_MAIN_2 0 n$1_0 x.0$1_0 1 n$2_0 x.0$2_0)))
(rule
 (=>
  (and (INV_MAIN_2 i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0)
       (<= i.1$1_0 n$1_0)
       (<= i.1$2_0 n$2_0))
  (INV_MAIN_2 (+ i.1$1_0 1) n$1_0 (+ x.1$1_0 i.1$1_0) (+ i.1$2_0 1) n$2_0 (+ x.1$2_0 i.1$2_0))))
(rule
 (=>
  (and (INV_MAIN_2 i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0)
       (<= i.1$1_0 n$1_0)
       (not (<= i.1$2_0 n$2_0)))
  (INV_MAIN_2 (+ i.1$1_0 1) n$1_0 (+ x.1$1_0 i.1$1_0) i.1$2_0 n$2_0 x.1$2_0)))
(rule
 (=>
  (and (INV_MAIN_2 i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0)
       (<= i.1$2_0 n$2_0)
       (not (<= i.1$1_0 n$1_0)))
  (INV_MAIN_2 i.1$1_0 n$1_0 x.1$1_0 (+ i.1$2_0 1) n$2_0 (+ x.1$2_0 i.1$2_0))))
(rule
 (=>
  (and (INV_MAIN_2 i.1$1_0 n$1_0 x.1$1_0 i.1$2_0 n$2_0 x.1$2_0)
       (not (<= i.1$1_0 n$1_0))
       (not (<= i.1$2_0 n$2_0)))
  (INV_MAIN_3 1 n$1_0 x.1$1_0 1 n$2_0 x.1$2_0)))

(rule
 (=>
  (and (INV_MAIN_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)
       (<= i.2$1_0 n$1_0)
       (<= i.2$2_0 n$2_0))
  (INV_MAIN_3 (+ i.2$1_0 1) n$1_0 (* x.2$1_0 2) (+ i.2$2_0 1) n$2_0 (* x.2$2_0 2))))
(rule
 (=>
  (and (INV_MAIN_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)
       (<= i.2$1_0 n$1_0)
       (not (<= i.2$2_0 n$2_0)))
  (INV_MAIN_3 (+ i.2$1_0 1) n$1_0 (* x.2$1_0 2) i.2$2_0 n$2_0 x.2$2_0)))
(rule
 (=>
  (and (INV_MAIN_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)
       (<= i.2$2_0 n$2_0)
       (not (<= i.2$1_0 n$1_0)))
  (INV_MAIN_3 i.2$1_0 n$1_0 x.2$1_0 (+ i.2$2_0 1) n$2_0 (* x.2$2_0 2))))
(rule
 (=>
  (and (INV_MAIN_3 i.2$1_0 n$1_0 x.2$1_0 i.2$2_0 n$2_0 x.2$2_0)
       (not (<= i.2$1_0 n$1_0))
       (not (<= i.2$2_0 n$2_0))
       (not (= x.2$1_0 x.2$2_0))
       )
  END))
(query END :print-certificate true)
