(set-option :int-real-coercions false)
(declare-var HEAP$1 (Array Int Int))
(declare-var HEAP$2 (Array Int Int))
(declare-var dest$1 Int)
(declare-var dst.0$2 Int)
(declare-var src$2 Int)
(declare-var i.0$1 Int)
(declare-var len$2 Int)
(declare-var len.addr.0$2 Int)
(declare-var mul$1 Int)
(declare-var nbytes$1 Int)
(declare-var src$1 Int)
(declare-var src.0$2 Int)
(declare-var to$2 Int)
(declare-rel
 END_QUERY
 ())
(declare-rel
   INV_MAIN
   (Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int (Array Int Int)))
(rule
 (=>
  (and
   (= src$1 src$2)
   (= dest$1 to$2)
   (= nbytes$1 len$2)
   (= HEAP$1 HEAP$2)
   (<= (+ src$1 nbytes$1) dest$1))
  (INV_MAIN dest$1 0 (* (div nbytes$1 2) 2) nbytes$1 src$1 HEAP$1 to$2 src$2 len$2 len$2 src$2 to$2 HEAP$2)))
(rule
 (=>
  (and
   (INV_MAIN dest$1 i.0$1 mul$1 nbytes$1 src$1 HEAP$1 dst.0$2 src$2 len$2 len.addr.0$2 src.0$2 to$2 HEAP$2)
   (not (< i.0$1 mul$1))
   (not (> len.addr.0$2 1))
   (not (= HEAP$1 HEAP$2)))
  END_QUERY))
(rule
 (=>
  (and
   (INV_MAIN dest$1 i.0$1 mul$1 nbytes$1 src$1 HEAP$1 dst.0$2 src$2 len$2 len.addr.0$2 src.0$2 to$2 HEAP$2)
   (< i.0$1 mul$1)
   (> len.addr.0$2 1))
  (INV_MAIN dest$1
            (+ i.0$1 2)
            mul$1
            nbytes$1
            src$1
            (store (store HEAP$1
                          (+ dest$1 i.0$1)
                          (select HEAP$1 (+ src$1 (+ i.0$1 1))))
                   (+ dest$1 (+ i.0$1 1))
                   (select (store HEAP$1
                                  (+ dest$1 i.0$1)
                                  (select HEAP$1 (+ src$1 (+ i.0$1 1))))
                           (+ src$1 i.0$1)))
            (+ dst.0$2 2)
            src$2
            len$2
            (- len.addr.0$2 2)
            (+ src.0$2 2)
            to$2
            (store (store HEAP$2
                          (+ dst.0$2 0)
                          (select HEAP$2 (+ src.0$2 1)))
                   (+ dst.0$2 1)
                   (select HEAP$2 (+ src.0$2 0))))))
(query
   END_QUERY
   :print-certificate
   true)
