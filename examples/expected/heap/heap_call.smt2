(set-logic HORN)
(define-fun
   IN_INV
   ((a$1_0 Int)
    (b$1_0 Int)
    (a$2_0 Int)
    (b$2_0 Int))
   Bool
   (and
      (= a$1_0 a$2_0)
      (= b$1_0 b$2_0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(declare-fun
   INV_REC_f
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_g
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_g_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_g__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_g__1_PRE
   (Int)
   Bool)
(declare-fun
   INV_REC_g__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_g__2_PRE
   (Int)
   Bool)
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (a$2_0_old Int)
       (b$2_0_old Int))
      (=>
         (IN_INV
            a$1_0_old
            b$1_0_old
            a$2_0_old
            b$2_0_old)
         (and
            (INV_REC_g_PRE b$1_0_old b$2_0_old)
            (forall
               ((_$1_0 Int)
                (_$2_0 Int))
               (=>
                  (INV_REC_g b$1_0_old b$2_0_old _$1_0 _$2_0)
                  (let
                     ((_$1_1 (select HEAP$1_old b$1_0_old)))
                     (let
                        ((result$1 _$1_1)
                         (_$2_1 (select HEAP$2_old b$2_0_old)))
                        (let
                           ((result$2 _$2_1))
                           (OUT_INV
                              result$1
                              result$2))))))))))
; forbidden main
; offbyn main
; end
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (a$2_0_old Int)
       (b$2_0_old Int))
      (=>
         (INV_REC_f_PRE a$1_0_old b$1_0_old a$2_0_old b$2_0_old)
         (and
            (INV_REC_g_PRE b$1_0_old b$2_0_old)
            (forall
               ((_$1_0 Int)
                (_$2_0 Int))
               (=>
                  (INV_REC_g b$1_0_old b$2_0_old _$1_0 _$2_0)
                  (let
                     ((_$1_1 (select HEAP$1_old b$1_0_old)))
                     (let
                        ((result$1 _$1_1)
                         (_$2_1 (select HEAP$2_old b$2_0_old)))
                        (let
                           ((result$2 _$2_1))
                           (INV_REC_f a$1_0_old b$1_0_old a$2_0_old b$2_0_old result$1 result$2))))))))))
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE a$1_0_old b$1_0_old)
         (and
            (INV_REC_g__1_PRE b$1_0_old)
            (forall
               ((_$1_0 Int))
               (=>
                  (INV_REC_g__1 b$1_0_old _$1_0)
                  (let
                     ((_$1_1 (select HEAP$1_old b$1_0_old)))
                     (let
                        ((result$1 _$1_1))
                        (INV_REC_f__1 a$1_0_old b$1_0_old result$1)))))))))
(assert
   (forall
      ((a$2_0_old Int)
       (b$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE a$2_0_old b$2_0_old)
         (and
            (INV_REC_g__2_PRE b$2_0_old)
            (forall
               ((_$2_0 Int))
               (=>
                  (INV_REC_g__2 b$2_0_old _$2_0)
                  (let
                     ((_$2_1 (select HEAP$2_old b$2_0_old)))
                     (let
                        ((result$2 _$2_1))
                        (INV_REC_f__2 a$2_0_old b$2_0_old result$2)))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((b$1_0_old Int)
       (b$2_0_old Int))
      (=>
         (INV_REC_g_PRE b$1_0_old b$2_0_old)
         (let
            ((HEAP$1 (store HEAP$1_old b$1_0_old 1))
             (result$1 0)
             (HEAP$2 (store HEAP$2_old b$2_0_old 1))
             (result$2 0))
            (INV_REC_g b$1_0_old b$2_0_old result$1 result$2)))))
(assert
   (forall
      ((b$1_0_old Int))
      (=>
         (INV_REC_g__1_PRE b$1_0_old)
         (let
            ((HEAP$1 (store HEAP$1_old b$1_0_old 1))
             (result$1 0))
            (INV_REC_g__1 b$1_0_old result$1)))))
(assert
   (forall
      ((b$2_0_old Int))
      (=>
         (INV_REC_g__2_PRE b$2_0_old)
         (let
            ((HEAP$2 (store HEAP$2_old b$2_0_old 1))
             (result$2 0))
            (INV_REC_g__2 b$2_0_old result$2)))))
; FORBIDDEN PATHS
; OFF BY N
(check-sat)
(get-model)
