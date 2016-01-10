(set-logic HORN)
(define-fun
   IN_INV
   ((instance$1_0 Int)
    (HEAP$1 (Array Int Int))
    (instance$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= instance$1_0 instance$2_0)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
(define-fun
   INV_REC_calloc
   ((arg1_0 Int)
    (arg1_1 Int)
    (HEAP$1 (Array Int Int))
    (arg2_0 Int)
    (arg2_1 Int)
    (HEAP$2 (Array Int Int))
    (res1 Int)
    (res2 Int)
    (HEAP$1_res (Array Int Int))
    (HEAP$2_res (Array Int Int)))
   Bool
   (=>
      (and
         (= arg1_0 arg2_0)
         (= arg1_1 arg2_1)
         (forall
            ((i Int))
            (= (select HEAP$1 i) (select HEAP$2 i))))
      (and
         (= res1 res2)
         (forall
            ((i Int))
            (= (select HEAP$1_res i) (select HEAP$2_res i))))))
(define-fun
   INV_REC_calloc__1
   ((arg1_0 Int)
    (arg1_1 Int)
    (HEAP (Array Int Int))
    (res Int)
    (HEAP_res (Array Int Int)))
   Bool
   true)
(define-fun
   INV_REC_calloc__2
   ((arg2_0 Int)
    (arg2_1 Int)
    (HEAP (Array Int Int))
    (res Int)
    (HEAP_res (Array Int Int)))
   Bool
   true)
                                        ; (INV_0_MAIN instance$1_0 r.0$1_0 i1 (select HEAP$1 i1) instance$2_0 r.0$2_0 i2 (select HEAP$2 i2))
(declare-fun
 INV_0_MAIN_UNDEF
 (Int
  Int
  Int
  Int
  Int
  Int
  Int
  Int)
 Bool)
(define-fun
  INV_0_MAIN
  ((instance$1_0 Int)
   (r.0$1_0 Int)
   (i1 Int)
   (heap1 Int)
   (instance$2_0 Int)
   (r.0$2_0 Int)
   (i2 Int)
   (heap2 Int))
  Bool
  (and (= instance$1_0 instance$2_0)
       (= r.0$1_0 r.0$2_0)
       (or (distinct i1 i2)
           (= heap1 heap2))
       (INV_0_MAIN_UNDEF instance$1_0 r.0$1_0 i1 heap1 instance$2_0 r.0$2_0 i2 heap2)))
(assert
   (forall
      ((instance$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (instance$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV
            instance$1_0_old
            HEAP$1_old
            instance$2_0_old
            HEAP$2_old)
         (let
            ((_$1_0 (+ instance$1_0_old (* 9 0) 5)))
            (let
               ((_$1_1 (select HEAP$1_old _$1_0)))
               (let
                  ((_$1_2 _$1_1)
                   (HEAP$1 HEAP$1_old)
                   (_$2_0 (+ instance$2_0_old (* 9 0) 5)))
                  (let
                     ((_$2_1 (select HEAP$2_old _$2_0)))
                     (let
                        ((_$2_2 _$2_1)
                         (HEAP$2 HEAP$2_old))
                        (forall
                           ((_$1_3 Int)
                            (_$2_3 Int)
                            (HEAP$1_res (Array Int Int))
                            (HEAP$2_res (Array Int Int)))
                           (=>
                              (INV_REC_calloc _$1_2 8 HEAP$1 _$2_2 8 HEAP$2 _$1_3 _$2_3 HEAP$1_res HEAP$2_res)
                              (let
                                 ((HEAP$1 HEAP$1_res)
                                  (_$1_4 _$1_3))
                                 (let
                                    ((_$1_5 (= _$1_4 0)))
                                    (=>
                                       _$1_5
                                       (let
                                          ((result$1 0)
                                           (HEAP$1_res HEAP$1)
                                           (instance$1_0 instance$1_0_old)
                                           (HEAP$2 HEAP$2_res)
                                           (_$2_4 _$2_3))
                                          (let
                                             ((_$2_5 (= _$2_4 0)))
                                             (=>
                                                _$2_5
                                                (let
                                                   ((result$2 0)
                                                    (HEAP$2_res HEAP$2)
                                                    (instance$2_0 instance$2_0_old))
                                                   (OUT_INV
                                                      result$1
                                                      result$2
                                                      HEAP$1_res
                                                      HEAP$2_res))))))))))))))))))
(assert
   (forall
      ((instance$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (instance$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV
            instance$1_0_old
            HEAP$1_old
            instance$2_0_old
            HEAP$2_old)
         (let
            ((_$1_0 (+ instance$1_0_old (* 9 0) 5)))
            (let
               ((_$1_1 (select HEAP$1_old _$1_0)))
               (let
                  ((_$1_2 _$1_1)
                   (HEAP$1 HEAP$1_old)
                   (_$2_0 (+ instance$2_0_old (* 9 0) 5)))
                  (let
                     ((_$2_1 (select HEAP$2_old _$2_0)))
                     (let
                        ((_$2_2 _$2_1)
                         (HEAP$2 HEAP$2_old))
                        (forall
                           ((_$1_3 Int)
                            (_$2_3 Int)
                            (HEAP$1_res (Array Int Int))
                            (HEAP$2_res (Array Int Int)))
                           (=>
                              (INV_REC_calloc _$1_2 8 HEAP$1 _$2_2 8 HEAP$2 _$1_3 _$2_3 HEAP$1_res HEAP$2_res)
                              (let
                                 ((HEAP$1 HEAP$1_res)
                                  (_$1_4 _$1_3))
                                 (let
                                    ((_$1_5 (= _$1_4 0)))
                                    (=>
                                       (not _$1_5)
                                       (let
                                          ((r.0$1_0 0)
                                           (instance$1_0 instance$1_0_old)
                                           (HEAP$2 HEAP$2_res)
                                           (_$2_4 _$2_3))
                                          (let
                                             ((_$2_5 (= _$2_4 0)))
                                             (=>
                                                (not _$2_5)
                                                (let
                                                   ((r.0$2_0 0)
                                                    (instance$2_0 instance$2_0_old))
                                                   (forall
                                                      ((i1 Int)
                                                       (i2 Int))
                                                      (INV_0_MAIN instance$1_0 r.0$1_0 i1 (select HEAP$1 i1) instance$2_0 r.0$2_0 i2 (select HEAP$2 i2))))))))))))))))))))
(assert
   (forall
      ((instance$1_0_old Int)
       (r.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (instance$2_0_old Int)
       (r.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_0_MAIN instance$1_0_old r.0$1_0_old i1 (select HEAP$1_old i1) instance$2_0_old r.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_7 (+ instance$1_0_old (* 9 0) 1)))
            (let
               ((_$1_8 (select HEAP$1_old _$1_7)))
               (let
                  ((_$1_9 (< r.0$1_0_old _$1_8)))
                  (=>
                     (not _$1_9)
                     (let
                        ((result$1 0)
                         (HEAP$1_res HEAP$1_old)
                         (instance$1_0 instance$1_0_old)
                         (r.0$1_0 r.0$1_0_old)
                         (HEAP$1 HEAP$1_old)
                         (_$2_7 (+ instance$2_0_old (* 9 0) 1)))
                        (let
                           ((_$2_8 (select HEAP$2_old _$2_7)))
                           (let
                              ((_$2_9 (< r.0$2_0_old _$2_8)))
                              (=>
                                 (not _$2_9)
                                 (let
                                    ((result$2 0)
                                     (HEAP$2_res HEAP$2_old)
                                     (instance$2_0 instance$2_0_old)
                                     (r.0$2_0 r.0$2_0_old)
                                     (HEAP$2 HEAP$2_old))
                                    (OUT_INV
                                       result$1
                                       result$2
                                       HEAP$1_res
                                       HEAP$2_res)))))))))))))
(assert
   (forall
      ((instance$1_0_old Int)
       (r.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (instance$2_0_old Int)
       (r.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_0_MAIN instance$1_0_old r.0$1_0_old i1 (select HEAP$1_old i1) instance$2_0_old r.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_7 (+ instance$1_0_old (* 9 0) 1)))
            (let
               ((_$1_8 (select HEAP$1_old _$1_7)))
               (let
                  ((_$1_9 (< r.0$1_0_old _$1_8)))
                  (=>
                     _$1_9
                     (let
                        ((_$1_13 (+ r.0$1_0_old 1)))
                        (let
                           ((r.0$1_0 _$1_13)
                            (instance$1_0 instance$1_0_old)
                            (HEAP$1 HEAP$1_old)
                            (_$2_7 (+ instance$2_0_old (* 9 0) 1)))
                           (let
                              ((_$2_8 (select HEAP$2_old _$2_7)))
                              (let
                                 ((_$2_9 (< r.0$2_0_old _$2_8)))
                                 (=>
                                    _$2_9
                                    (let
                                       ((_$2_13 (+ r.0$2_0_old 1)))
                                       (let
                                          ((r.0$2_0 _$2_13)
                                           (instance$2_0 instance$2_0_old)
                                           (HEAP$2 HEAP$2_old))
                                          (forall
                                             ((i1 Int)
                                              (i2 Int))
                                             (INV_0_MAIN instance$1_0 r.0$1_0 i1 (select HEAP$1 i1) instance$2_0 r.0$2_0 i2 (select HEAP$2 i2)))))))))))))))))
; forbidden main
(assert
   (forall
      ((instance$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (instance$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV
            instance$1_0_old
            HEAP$1_old
            instance$2_0_old
            HEAP$2_old)
         (let
            ((_$1_0 (+ instance$1_0_old (* 9 0) 5)))
            (let
               ((_$1_1 (select HEAP$1_old _$1_0)))
               (let
                  ((_$1_2 _$1_1)
                   (HEAP$1 HEAP$1_old))
                  (forall
                     ((_$1_3 Int)
                      (HEAP$1_res (Array Int Int)))
                     (=>
                        (INV_REC_calloc__1 _$1_2 8 HEAP$1 _$1_3 HEAP$1_res)
                        (let
                           ((HEAP$1 HEAP$1_res)
                            (_$1_4 _$1_3))
                           (let
                              ((_$1_5 (= _$1_4 0)))
                              (=>
                                 _$1_5
                                 (let
                                    ((result$1 0)
                                     (HEAP$1_res HEAP$1)
                                     (_$2_0 (+ instance$2_0_old (* 9 0) 5)))
                                    (let
                                       ((_$2_1 (select HEAP$2_old _$2_0)))
                                       (let
                                          ((_$2_2 _$2_1)
                                           (HEAP$2 HEAP$2_old))
                                          (forall
                                             ((_$2_3 Int)
                                              (HEAP$2_res (Array Int Int)))
                                             (=>
                                                (INV_REC_calloc__2 _$2_2 8 HEAP$2 _$2_3 HEAP$2_res)
                                                (let
                                                   ((HEAP$2 HEAP$2_res)
                                                    (_$2_4 _$2_3))
                                                   (let
                                                      ((_$2_5 (= _$2_4 0)))
                                                      (=>
                                                         (not _$2_5)
                                                         (let
                                                            ((r.0$2_0 0))
                                                            false))))))))))))))))))))
(assert
   (forall
      ((instance$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (instance$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV
            instance$1_0_old
            HEAP$1_old
            instance$2_0_old
            HEAP$2_old)
         (let
            ((_$1_0 (+ instance$1_0_old (* 9 0) 5)))
            (let
               ((_$1_1 (select HEAP$1_old _$1_0)))
               (let
                  ((_$1_2 _$1_1)
                   (HEAP$1 HEAP$1_old))
                  (forall
                     ((_$1_3 Int)
                      (HEAP$1_res (Array Int Int)))
                     (=>
                        (INV_REC_calloc__1 _$1_2 8 HEAP$1 _$1_3 HEAP$1_res)
                        (let
                           ((HEAP$1 HEAP$1_res)
                            (_$1_4 _$1_3))
                           (let
                              ((_$1_5 (= _$1_4 0)))
                              (=>
                                 (not _$1_5)
                                 (let
                                    ((r.0$1_0 0)
                                     (_$2_0 (+ instance$2_0_old (* 9 0) 5)))
                                    (let
                                       ((_$2_1 (select HEAP$2_old _$2_0)))
                                       (let
                                          ((_$2_2 _$2_1)
                                           (HEAP$2 HEAP$2_old))
                                          (forall
                                             ((_$2_3 Int)
                                              (HEAP$2_res (Array Int Int)))
                                             (=>
                                                (INV_REC_calloc__2 _$2_2 8 HEAP$2 _$2_3 HEAP$2_res)
                                                (let
                                                   ((HEAP$2 HEAP$2_res)
                                                    (_$2_4 _$2_3))
                                                   (let
                                                      ((_$2_5 (= _$2_4 0)))
                                                      (=>
                                                         _$2_5
                                                         (let
                                                            ((result$2 0)
                                                             (HEAP$2_res HEAP$2))
                                                            false))))))))))))))))))))
(assert
   (forall
      ((instance$1_0_old Int)
       (r.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (instance$2_0_old Int)
       (r.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_0_MAIN instance$1_0_old r.0$1_0_old i1 (select HEAP$1_old i1) instance$2_0_old r.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_7 (+ instance$1_0_old (* 9 0) 1)))
            (let
               ((_$1_8 (select HEAP$1_old _$1_7)))
               (let
                  ((_$1_9 (< r.0$1_0_old _$1_8)))
                  (=>
                     (not _$1_9)
                     (let
                        ((result$1 0)
                         (HEAP$1_res HEAP$1_old)
                         (_$2_7 (+ instance$2_0_old (* 9 0) 1)))
                        (let
                           ((_$2_8 (select HEAP$2_old _$2_7)))
                           (let
                              ((_$2_9 (< r.0$2_0_old _$2_8)))
                              (=>
                                 _$2_9
                                 (let
                                    ((_$2_13 (+ r.0$2_0_old 1)))
                                    (let
                                       ((r.0$2_0 _$2_13))
                                       false)))))))))))))
(assert
   (forall
      ((instance$1_0_old Int)
       (r.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (instance$2_0_old Int)
       (r.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1 Int)
             (i2 Int))
            (INV_0_MAIN instance$1_0_old r.0$1_0_old i1 (select HEAP$1_old i1) instance$2_0_old r.0$2_0_old i2 (select HEAP$2_old i2)))
         (let
            ((_$1_7 (+ instance$1_0_old (* 9 0) 1)))
            (let
               ((_$1_8 (select HEAP$1_old _$1_7)))
               (let
                  ((_$1_9 (< r.0$1_0_old _$1_8)))
                  (=>
                     _$1_9
                     (let
                        ((_$1_13 (+ r.0$1_0_old 1)))
                        (let
                           ((r.0$1_0 _$1_13)
                            (_$2_7 (+ instance$2_0_old (* 9 0) 1)))
                           (let
                              ((_$2_8 (select HEAP$2_old _$2_7)))
                              (let
                                 ((_$2_9 (< r.0$2_0_old _$2_8)))
                                 (=>
                                    (not _$2_9)
                                    (let
                                       ((result$2 0)
                                        (HEAP$2_res HEAP$2_old))
                                       false)))))))))))))
; end
(check-sat)
(get-model)
