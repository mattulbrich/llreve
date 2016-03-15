(set-logic HORN)
(declare-fun INV_MAIN_42 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
(assert
 (forall ((n1 (_ BitVec 8)) (i2 (_ BitVec 8)))
         (=> (= n1 i2)
             (bvsge n1 (_ bv0 8))
             (bvslt n1 (_ bv15 8))
             (INV_MAIN_42 (_ bv0 8) (_ bv0 8) n1 i2 (_ bv0 8)))))
(assert
 (forall ((j1 (_ BitVec 8)) (j2 (_ BitVec 8)) (i2 (_ BitVec 8)) (n1 (_ BitVec 8)) (i1 (_ BitVec 8)))
         (=> (and (not (bvsge i2 (_ bv0 8))) (not (bvsge n1 i1)) (INV_MAIN_42 i1 j1 n1 i2 j2))
             (= j1 j2))))
(assert
 (forall ((n1 (_ BitVec 8)) (i1 (_ BitVec 8)) (j1 (_ BitVec 8)) (i2 (_ BitVec 8)) (j2 (_ BitVec 8)))
         (=> (and (bvsge i2 (_ bv0 8)) (bvsge n1 i1) (INV_MAIN_42 i1 j1 n1 i2 j2))
             (INV_MAIN_42 (bvadd i1 (_ bv1 8)) (bvadd j1 (_ bv1 8)) n1 (bvsub i2 (_ bv1 8)) (bvadd j2 (_ bv1 8))))))
(assert
 (forall ((i2 (_ BitVec 8)) (n1 (_ BitVec 8)) (i1 (_ BitVec 8)) (j1 (_ BitVec 8)) (j2 (_ BitVec 8)))
         (=> (and (bvsge i2 (_ bv0 8)) (not (bvsge n1 i1)) (INV_MAIN_42 i1 j1 n1 i2 j2))
             false)))
(assert
 (forall ((i2 (_ BitVec 8)) (n1 (_ BitVec 8)) (i1 (_ BitVec 8)) (j1 (_ BitVec 8)) (j2 (_ BitVec 8)))
         (=> (and (not (bvsge i2 (_ bv0 8))) (bvsge n1 i1) (INV_MAIN_42 i1 j1 n1 i2 j2))
             false)))
(check-sat)
(get-model)
