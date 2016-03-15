(set-logic HORN)
(declare-fun INV_MAIN_42 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(assert
 (forall ((n1 (_ BitVec 32)) (j2 (_ BitVec 32)))
         (=> (= n1 j2)
             (bvsge n1 (_ bv0 32))
             ;; This needs to be bigger than half of the bitvector size, otherwise some other technique seems to be used.
             (bvslt n1 (_ bv2147483648 32))
             (INV_MAIN_42 (_ bv0 32) (_ bv0 32) n1 j2 (_ bv0 32)))))
(assert
 (forall ((j1 (_ BitVec 32)) (j2 (_ BitVec 32)) (i2 (_ BitVec 32)) (n1 (_ BitVec 32)) (i1 (_ BitVec 32)))
         (=> (and (not (bvsge i2 (_ bv0 32))) (not (bvsge n1 i1)) (INV_MAIN_42 i1 j1 n1 i2 j2))
             (= j1 j2))))
(assert
 (forall ((n1 (_ BitVec 32)) (i1 (_ BitVec 32)) (j1 (_ BitVec 32)) (i2 (_ BitVec 32)) (j2 (_ BitVec 32)))
         (=> (and (bvsge i2 (_ bv0 32)) (bvsge n1 i1) (INV_MAIN_42 i1 j1 n1 i2 j2))
             (INV_MAIN_42 (bvadd i1 (_ bv1 32)) (bvadd j1 (_ bv1 32)) n1 (bvsub i2 (_ bv1 32)) (bvadd j2 (_ bv1 32))))))
(assert
 (forall ((i2 (_ BitVec 32)) (n1 (_ BitVec 32)) (i1 (_ BitVec 32)) (j1 (_ BitVec 32)) (j2 (_ BitVec 32)))
         (=> (and (bvsge i2 (_ bv0 32)) (not (bvsge n1 i1)) (INV_MAIN_42 i1 j1 n1 i2 j2))
             false)))
(assert
 (forall ((i2 (_ BitVec 32)) (n1 (_ BitVec 32)) (i1 (_ BitVec 32)) (j1 (_ BitVec 32)) (j2 (_ BitVec 32)))
         (=> (and (not (bvsge i2 (_ bv0 32))) (bvsge n1 i1) (INV_MAIN_42 i1 j1 n1 i2 j2))
             false)))
(check-sat)
(get-model)
