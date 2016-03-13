(set-logic HORN)
(declare-fun INV_MAIN_42 ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)) Bool)
(assert
 (forall ((n1 (_ BitVec 16)) (j2 (_ BitVec 16)))
         (=> (= n1 j2)
             (bvsge n1 (_ bv0 16))
             (bvslt n1 (_ bv65535 16))
             (INV_MAIN_42 (_ bv0 16) (_ bv0 16) n1 j2 (_ bv0 16)))))
(assert
 (forall ((j1 (_ BitVec 16)) (j2 (_ BitVec 16)) (i2 (_ BitVec 16)) (n1 (_ BitVec 16)) (i1 (_ BitVec 16)))
         (=> (and (not (bvsge i2 (_ bv0 16))) (not (bvsge n1 i1)) (INV_MAIN_42 i1 j1 n1 i2 j2))
             (= j1 j2))))
(assert
 (forall ((n1 (_ BitVec 16)) (i1 (_ BitVec 16)) (j1 (_ BitVec 16)) (i2 (_ BitVec 16)) (j2 (_ BitVec 16)))
         (=> (and (bvsge i2 (_ bv0 16)) (bvsge n1 i1) (INV_MAIN_42 i1 j1 n1 i2 j2))
             (INV_MAIN_42 (bvadd i1 (_ bv1 16)) (bvadd j1 (_ bv1 16)) n1 (bvsub i2 (_ bv1 16)) (bvadd j2 (_ bv1 16))))))
(assert
 (forall ((i2 (_ BitVec 16)) (n1 (_ BitVec 16)) (i1 (_ BitVec 16)) (j1 (_ BitVec 16)) (j2 (_ BitVec 16)))
         (=> (and (bvsge i2 (_ bv0 16)) (not (bvsge n1 i1)) (INV_MAIN_42 i1 j1 n1 i2 j2))
             false)))
(assert
 (forall ((i2 (_ BitVec 16)) (n1 (_ BitVec 16)) (i1 (_ BitVec 16)) (j1 (_ BitVec 16)) (j2 (_ BitVec 16)))
         (=> (and (not (bvsge i2 (_ bv0 16))) (bvsge n1 i1) (INV_MAIN_42 i1 j1 n1 i2 j2))
             false)))
(check-sat)
(get-model)
