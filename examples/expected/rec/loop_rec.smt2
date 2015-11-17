(set-logic HORN)
(declare-fun
   INV_REC_f
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1_PRE
   (Int)
   Bool)
(declare-fun
   INV_REC_f__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2_PRE
   (Int)
   Bool)
(declare-fun
   INV_REC_tr
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_tr_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_tr__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_tr__1_PRE
   (Int)
   Bool)
(declare-fun
   INV_REC_tr__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_tr__2_PRE
   (Int)
   Bool)
(declare-fun
   INV_42
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42_PRE
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__1_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_42__2
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_42__2_PRE
   (Int
    Int)
   Bool)
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (and
            (= m$1_0_old m$2_0_old))
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- m$1_0_old 1))
                   (_$2_0 (> m$2_0_old 0)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (- m$2_0_old 1)))
                        (and
                           (INV_REC_tr_PRE _$1_1 _$2_1)
                           (forall
                              ((_$1_2 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_tr _$1_1 _$2_1 _$1_2 _$2_2)
                                 (let
                                    ((_$1_1 (- m$1_0_old 1))
                                     (_$1_3 (+ _$1_2 m$1_0_old)))
                                    (let
                                       ((result.0$1_0 _$1_3))
                                       (let
                                          ((result$1 result.0$1_0)
                                           (_$2_1 (- m$2_0_old 1))
                                           (_$2_3 (>= _$2_2 0)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_4 (+ _$2_2 m$2_0_old)))
                                                (let
                                                   ((result.0$2_0 _$2_4))
                                                   (let
                                                      ((result.1$2_0 result.0$2_0))
                                                      (let
                                                         ((result$2 result.1$2_0))
                                                         (= result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (and
            (= m$1_0_old m$2_0_old))
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- m$1_0_old 1))
                   (_$2_0 (> m$2_0_old 0)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (- m$2_0_old 1)))
                        (and
                           (INV_REC_tr_PRE _$1_1 _$2_1)
                           (forall
                              ((_$1_2 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_tr _$1_1 _$2_1 _$1_2 _$2_2)
                                 (let
                                    ((_$1_1 (- m$1_0_old 1))
                                     (_$1_3 (+ _$1_2 m$1_0_old)))
                                    (let
                                       ((result.0$1_0 _$1_3))
                                       (let
                                          ((result$1 result.0$1_0)
                                           (_$2_1 (- m$2_0_old 1))
                                           (_$2_3 (>= _$2_2 0)))
                                          (=>
                                             (not _$2_3)
                                             (let
                                                ((result.0$2_0 _$2_2))
                                                (let
                                                   ((result.1$2_0 result.0$2_0))
                                                   (let
                                                      ((result$2 result.1$2_0))
                                                      (= result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (and
            (= m$1_0_old m$2_0_old))
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- m$1_0_old 1))
                   (_$2_0 (> m$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((result.1$2_0 0))
                        (let
                           ((result$2 result.1$2_0))
                           (and
                              (INV_REC_tr__1_PRE _$1_1)
                              (forall
                                 ((_$1_2 Int))
                                 (=>
                                    (INV_REC_tr__1 _$1_1 _$1_2)
                                    (let
                                       ((_$1_1 (- m$1_0_old 1))
                                        (_$1_3 (+ _$1_2 m$1_0_old)))
                                       (let
                                          ((result.0$1_0 _$1_3))
                                          (let
                                             ((result$1 result.0$1_0))
                                             (= result$1 result$2))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (and
            (= m$1_0_old m$2_0_old))
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((result.0$1_0 0))
                  (let
                     ((result$1 result.0$1_0)
                      (_$2_0 (> m$2_0_old 0)))
                     (=>
                        _$2_0
                        (let
                           ((_$2_1 (- m$2_0_old 1)))
                           (and
                              (INV_REC_tr__2_PRE _$2_1)
                              (forall
                                 ((_$2_2 Int))
                                 (=>
                                    (INV_REC_tr__2 _$2_1 _$2_2)
                                    (let
                                       ((_$2_1 (- m$2_0_old 1))
                                        (_$2_3 (>= _$2_2 0)))
                                       (=>
                                          _$2_3
                                          (let
                                             ((_$2_4 (+ _$2_2 m$2_0_old)))
                                             (let
                                                ((result.0$2_0 _$2_4))
                                                (let
                                                   ((result.1$2_0 result.0$2_0))
                                                   (let
                                                      ((result$2 result.1$2_0))
                                                      (= result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (and
            (= m$1_0_old m$2_0_old))
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((result.0$1_0 0))
                  (let
                     ((result$1 result.0$1_0)
                      (_$2_0 (> m$2_0_old 0)))
                     (=>
                        _$2_0
                        (let
                           ((_$2_1 (- m$2_0_old 1)))
                           (and
                              (INV_REC_tr__2_PRE _$2_1)
                              (forall
                                 ((_$2_2 Int))
                                 (=>
                                    (INV_REC_tr__2 _$2_1 _$2_2)
                                    (let
                                       ((_$2_1 (- m$2_0_old 1))
                                        (_$2_3 (>= _$2_2 0)))
                                       (=>
                                          (not _$2_3)
                                          (let
                                             ((result.0$2_0 _$2_2))
                                             (let
                                                ((result.1$2_0 result.0$2_0))
                                                (let
                                                   ((result$2 result.1$2_0))
                                                   (= result$1 result$2))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (and
            (= m$1_0_old m$2_0_old))
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((result.0$1_0 0))
                  (let
                     ((result$1 result.0$1_0)
                      (_$2_0 (> m$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((result.1$2_0 0))
                           (let
                              ((result$2 result.1$2_0))
                              (= result$1 result$2)))))))))))
; forbidden main
; offbyn main
; end
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old m$2_0_old)
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- m$1_0_old 1))
                   (_$2_0 (> m$2_0_old 0)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (- m$2_0_old 1)))
                        (and
                           (INV_REC_tr_PRE _$1_1 _$2_1)
                           (forall
                              ((_$1_2 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_tr _$1_1 _$2_1 _$1_2 _$2_2)
                                 (let
                                    ((_$1_1 (- m$1_0_old 1))
                                     (_$1_3 (+ _$1_2 m$1_0_old)))
                                    (let
                                       ((result.0$1_0 _$1_3))
                                       (let
                                          ((result$1 result.0$1_0)
                                           (_$2_1 (- m$2_0_old 1))
                                           (_$2_3 (>= _$2_2 0)))
                                          (=>
                                             _$2_3
                                             (let
                                                ((_$2_4 (+ _$2_2 m$2_0_old)))
                                                (let
                                                   ((result.0$2_0 _$2_4))
                                                   (let
                                                      ((result.1$2_0 result.0$2_0))
                                                      (let
                                                         ((result$2 result.1$2_0))
                                                         (INV_REC_f m$1_0_old m$2_0_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old m$2_0_old)
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- m$1_0_old 1))
                   (_$2_0 (> m$2_0_old 0)))
                  (=>
                     _$2_0
                     (let
                        ((_$2_1 (- m$2_0_old 1)))
                        (and
                           (INV_REC_tr_PRE _$1_1 _$2_1)
                           (forall
                              ((_$1_2 Int)
                               (_$2_2 Int))
                              (=>
                                 (INV_REC_tr _$1_1 _$2_1 _$1_2 _$2_2)
                                 (let
                                    ((_$1_1 (- m$1_0_old 1))
                                     (_$1_3 (+ _$1_2 m$1_0_old)))
                                    (let
                                       ((result.0$1_0 _$1_3))
                                       (let
                                          ((result$1 result.0$1_0)
                                           (_$2_1 (- m$2_0_old 1))
                                           (_$2_3 (>= _$2_2 0)))
                                          (=>
                                             (not _$2_3)
                                             (let
                                                ((result.0$2_0 _$2_2))
                                                (let
                                                   ((result.1$2_0 result.0$2_0))
                                                   (let
                                                      ((result$2 result.1$2_0))
                                                      (INV_REC_f m$1_0_old m$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old m$2_0_old)
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- m$1_0_old 1))
                   (_$2_0 (> m$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((result.1$2_0 0))
                        (let
                           ((result$2 result.1$2_0))
                           (and
                              (INV_REC_tr__1_PRE _$1_1)
                              (forall
                                 ((_$1_2 Int))
                                 (=>
                                    (INV_REC_tr__1 _$1_1 _$1_2)
                                    (let
                                       ((_$1_1 (- m$1_0_old 1))
                                        (_$1_3 (+ _$1_2 m$1_0_old)))
                                       (let
                                          ((result.0$1_0 _$1_3))
                                          (let
                                             ((result$1 result.0$1_0))
                                             (INV_REC_f m$1_0_old m$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old m$2_0_old)
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((result.0$1_0 0))
                  (let
                     ((result$1 result.0$1_0)
                      (_$2_0 (> m$2_0_old 0)))
                     (=>
                        _$2_0
                        (let
                           ((_$2_1 (- m$2_0_old 1)))
                           (and
                              (INV_REC_tr__2_PRE _$2_1)
                              (forall
                                 ((_$2_2 Int))
                                 (=>
                                    (INV_REC_tr__2 _$2_1 _$2_2)
                                    (let
                                       ((_$2_1 (- m$2_0_old 1))
                                        (_$2_3 (>= _$2_2 0)))
                                       (=>
                                          _$2_3
                                          (let
                                             ((_$2_4 (+ _$2_2 m$2_0_old)))
                                             (let
                                                ((result.0$2_0 _$2_4))
                                                (let
                                                   ((result.1$2_0 result.0$2_0))
                                                   (let
                                                      ((result$2 result.1$2_0))
                                                      (INV_REC_f m$1_0_old m$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old m$2_0_old)
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((result.0$1_0 0))
                  (let
                     ((result$1 result.0$1_0)
                      (_$2_0 (> m$2_0_old 0)))
                     (=>
                        _$2_0
                        (let
                           ((_$2_1 (- m$2_0_old 1)))
                           (and
                              (INV_REC_tr__2_PRE _$2_1)
                              (forall
                                 ((_$2_2 Int))
                                 (=>
                                    (INV_REC_tr__2 _$2_1 _$2_2)
                                    (let
                                       ((_$2_1 (- m$2_0_old 1))
                                        (_$2_3 (>= _$2_2 0)))
                                       (=>
                                          (not _$2_3)
                                          (let
                                             ((result.0$2_0 _$2_2))
                                             (let
                                                ((result.1$2_0 result.0$2_0))
                                                (let
                                                   ((result$2 result.1$2_0))
                                                   (INV_REC_f m$1_0_old m$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (m$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old m$2_0_old)
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((result.0$1_0 0))
                  (let
                     ((result$1 result.0$1_0)
                      (_$2_0 (> m$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((result.1$2_0 0))
                           (let
                              ((result$2 result.1$2_0))
                              (INV_REC_f m$1_0_old m$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((m$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE m$1_0_old)
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (- m$1_0_old 1)))
                  (and
                     (INV_REC_tr__1_PRE _$1_1)
                     (forall
                        ((_$1_2 Int))
                        (=>
                           (INV_REC_tr__1 _$1_1 _$1_2)
                           (let
                              ((_$1_1 (- m$1_0_old 1))
                               (_$1_3 (+ _$1_2 m$1_0_old)))
                              (let
                                 ((result.0$1_0 _$1_3))
                                 (let
                                    ((result$1 result.0$1_0))
                                    (INV_REC_f__1 m$1_0_old result$1)))))))))))))
(assert
   (forall
      ((m$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE m$1_0_old)
         (let
            ((_$1_0 (> m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((result.0$1_0 0))
                  (let
                     ((result$1 result.0$1_0))
                     (INV_REC_f__1 m$1_0_old result$1))))))))
(assert
   (forall
      ((m$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old)
         (let
            ((_$2_0 (> m$2_0_old 0)))
            (=>
               _$2_0
               (let
                  ((_$2_1 (- m$2_0_old 1)))
                  (and
                     (INV_REC_tr__2_PRE _$2_1)
                     (forall
                        ((_$2_2 Int))
                        (=>
                           (INV_REC_tr__2 _$2_1 _$2_2)
                           (let
                              ((_$2_1 (- m$2_0_old 1))
                               (_$2_3 (>= _$2_2 0)))
                              (=>
                                 _$2_3
                                 (let
                                    ((_$2_4 (+ _$2_2 m$2_0_old)))
                                    (let
                                       ((result.0$2_0 _$2_4))
                                       (let
                                          ((result.1$2_0 result.0$2_0))
                                          (let
                                             ((result$2 result.1$2_0))
                                             (INV_REC_f__2 m$2_0_old result$2))))))))))))))))
(assert
   (forall
      ((m$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old)
         (let
            ((_$2_0 (> m$2_0_old 0)))
            (=>
               _$2_0
               (let
                  ((_$2_1 (- m$2_0_old 1)))
                  (and
                     (INV_REC_tr__2_PRE _$2_1)
                     (forall
                        ((_$2_2 Int))
                        (=>
                           (INV_REC_tr__2 _$2_1 _$2_2)
                           (let
                              ((_$2_1 (- m$2_0_old 1))
                               (_$2_3 (>= _$2_2 0)))
                              (=>
                                 (not _$2_3)
                                 (let
                                    ((result.0$2_0 _$2_2))
                                    (let
                                       ((result.1$2_0 result.0$2_0))
                                       (let
                                          ((result$2 result.1$2_0))
                                          (INV_REC_f__2 m$2_0_old result$2)))))))))))))))
(assert
   (forall
      ((m$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old)
         (let
            ((_$2_0 (> m$2_0_old 0)))
            (=>
               (not _$2_0)
               (let
                  ((result.1$2_0 0))
                  (let
                     ((result$2 result.1$2_0))
                     (INV_REC_f__2 m$2_0_old result$2))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_tr_PRE n$1_0_old n$2_0_old)
         (let
            ((result.0$1_0 0)
             (n$1_0 n$1_0_old)
             (result.0$2_0 0)
             (n$2_0 n$2_0_old))
            (forall
               ((result$1 Int)
                (result$2 Int))
               (and
                  (INV_42_PRE n$1_0 result.0$1_0 n$2_0 result.0$2_0)
                  (=>
                     (INV_42 n$1_0 result.0$1_0 n$2_0 result.0$2_0 result$1 result$2)
                     (INV_REC_tr n$1_0_old n$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (result.0$1_0_old Int)
       (n$2_0_old Int)
       (result.0$2_0_old Int))
      (=>
         (INV_42_PRE n$1_0_old result.0$1_0_old n$2_0_old result.0$2_0_old)
         (let
            ((_$1_1 (< 0 n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 result.0$1_0_old)
                   (_$2_1 (< 0 n$2_0_old)))
                  (=>
                     (not _$2_1)
                     (let
                        ((result$2 result.0$2_0_old))
                        (INV_42 n$1_0_old result.0$1_0_old n$2_0_old result.0$2_0_old result$1 result$2)))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (result.0$1_0_old Int)
       (n$2_0_old Int)
       (result.0$2_0_old Int))
      (=>
         (INV_42_PRE n$1_0_old result.0$1_0_old n$2_0_old result.0$2_0_old)
         (let
            ((_$1_1 (< 0 n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ result.0$1_0_old 0)))
                  (let
                     ((result.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old)
                      (_$2_1 (< 0 n$2_0_old)))
                     (=>
                        _$2_1
                        (let
                           ((_$2_5 (+ result.0$2_0_old 0)))
                           (let
                              ((result.0$2_0 _$2_5)
                               (n$2_0 n$2_0_old))
                              (forall
                                 ((result$1 Int)
                                  (result$2 Int))
                                 (and
                                    (INV_42_PRE n$1_0 result.0$1_0 n$2_0 result.0$2_0)
                                    (=>
                                       (INV_42 n$1_0 result.0$1_0 n$2_0 result.0$2_0 result$1 result$2)
                                       (INV_42 n$1_0_old result.0$1_0_old n$2_0_old result.0$2_0_old result$1 result$2))))))))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (=>
         (INV_REC_tr__1_PRE n$1_0_old)
         (let
            ((result.0$1_0 0)
             (n$1_0 n$1_0_old))
            (forall
               ((result$1 Int))
               (=>
                  (INV_42__1 n$1_0 result.0$1_0 result$1)
                  (INV_REC_tr__1 n$1_0_old result$1)))))))
(assert
   (forall
      ((n$1_0_old Int)
       (result.0$1_0_old Int))
      (=>
         (INV_42__1_PRE n$1_0_old result.0$1_0_old)
         (let
            ((_$1_1 (< 0 n$1_0_old)))
            (=>
               (not _$1_1)
               (let
                  ((result$1 result.0$1_0_old))
                  (INV_42__1 n$1_0_old result.0$1_0_old result$1)))))))
(assert
   (forall
      ((n$1_0_old Int)
       (result.0$1_0_old Int))
      (=>
         (INV_42__1_PRE n$1_0_old result.0$1_0_old)
         (let
            ((_$1_1 (< 0 n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ result.0$1_0_old 0)))
                  (let
                     ((result.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old))
                     (forall
                        ((result$1 Int))
                        (=>
                           (INV_42__1 n$1_0 result.0$1_0 result$1)
                           (INV_42__1 n$1_0_old result.0$1_0_old result$1))))))))))
(assert
   (forall
      ((n$2_0_old Int))
      (=>
         (INV_REC_tr__2_PRE n$2_0_old)
         (let
            ((result.0$2_0 0)
             (n$2_0 n$2_0_old))
            (forall
               ((result$2 Int))
               (=>
                  (INV_42__2 n$2_0 result.0$2_0 result$2)
                  (INV_REC_tr__2 n$2_0_old result$2)))))))
(assert
   (forall
      ((n$2_0_old Int)
       (result.0$2_0_old Int))
      (=>
         (INV_42__2_PRE n$2_0_old result.0$2_0_old)
         (let
            ((_$2_1 (< 0 n$2_0_old)))
            (=>
               (not _$2_1)
               (let
                  ((result$2 result.0$2_0_old))
                  (INV_42__2 n$2_0_old result.0$2_0_old result$2)))))))
(assert
   (forall
      ((n$2_0_old Int)
       (result.0$2_0_old Int))
      (=>
         (INV_42__2_PRE n$2_0_old result.0$2_0_old)
         (let
            ((_$2_1 (< 0 n$2_0_old)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ result.0$2_0_old 0)))
                  (let
                     ((result.0$2_0 _$2_5)
                      (n$2_0 n$2_0_old))
                     (forall
                        ((result$2 Int))
                        (=>
                           (INV_42__2 n$2_0 result.0$2_0 result$2)
                           (INV_42__2 n$2_0_old result.0$2_0_old result$2))))))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((n$1_0_old Int)
       (result.0$1_0_old Int)
       (n$2_0_old Int)
       (result.0$2_0_old Int))
      (=>
         (INV_42_PRE n$1_0_old result.0$1_0_old n$2_0_old result.0$2_0_old)
         (let
            ((_$1_1 (< 0 n$1_0_old)))
            (=>
               _$1_1
               (let
                  ((_$1_5 (+ result.0$1_0_old 0)))
                  (let
                     ((result.0$1_0 _$1_5)
                      (n$1_0 n$1_0_old))
                     (=>
                        (and
                           (let
                              ((_$2_1 (< 0 n$2_0_old)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_5 (+ result.0$2_0_old 0)))
                                    (let
                                       ((result.0$2_0 _$2_5)
                                        (n$2_0 n$2_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_42_PRE n$1_0 result.0$1_0 n$2_0_old result.0$2_0_old)
                              (=>
                                 (INV_42 n$1_0 result.0$1_0 n$2_0_old result.0$2_0_old result$1 result$2)
                                 (INV_42 n$1_0_old result.0$1_0_old n$2_0_old result.0$2_0_old result$1 result$2))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (result.0$1_0_old Int)
       (n$2_0_old Int)
       (result.0$2_0_old Int))
      (=>
         (INV_42_PRE n$1_0_old result.0$1_0_old n$2_0_old result.0$2_0_old)
         (let
            ((_$2_1 (< 0 n$2_0_old)))
            (=>
               _$2_1
               (let
                  ((_$2_5 (+ result.0$2_0_old 0)))
                  (let
                     ((result.0$2_0 _$2_5)
                      (n$2_0 n$2_0_old))
                     (=>
                        (and
                           (let
                              ((_$1_1 (< 0 n$1_0_old)))
                              (=>
                                 _$1_1
                                 (let
                                    ((_$1_5 (+ result.0$1_0_old 0)))
                                    (let
                                       ((result.0$1_0 _$1_5)
                                        (n$1_0 n$1_0_old))
                                       false)))))
                        (forall
                           ((result$1 Int)
                            (result$2 Int))
                           (and
                              (INV_42_PRE n$1_0_old result.0$1_0_old n$2_0 result.0$2_0)
                              (=>
                                 (INV_42 n$1_0_old result.0$1_0_old n$2_0 result.0$2_0 result$1 result$2)
                                 (INV_42 n$1_0_old result.0$1_0_old n$2_0_old result.0$2_0_old result$1 result$2))))))))))))
(check-sat)
(get-model)
