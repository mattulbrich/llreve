(set-logic HORN)
(declare-fun
   INV_REC_triangle
   (Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_triangle_PRE
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_triangle__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_triangle__2
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f
   (Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__1
   (Int
    Int)
   Bool)
(declare-fun
   INV_REC_f__2
   (Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((n$1_0 Int)
       (n$2_0 Int)
       (result$1 Int)
       (result$2 Int))
      (=>
         (and
            (= n$1_0 n$2_0))
         (and
            (=>
               (INV_REC_triangle n$1_0 n$2_0 result$1 result$2)
               (= result$1 result$2))
            (INV_REC_triangle_PRE n$1_0 n$2_0)))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_triangle_PRE n$1_0_old n$2_0_old)
         (and
            (INV_REC_f_PRE n$1_0_old n$2_0_old 0)
            (forall
               ((_$1_0 Int)
                (_$2_0 Int))
               (=>
                  (INV_REC_f n$1_0_old n$2_0_old 0 _$1_0 _$2_0)
                  (let
                     ((result$1 _$1_0)
                      (result$2 _$2_0))
                     (INV_REC_triangle n$1_0_old n$2_0_old result$1 result$2))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (forall
         ((_$1_0 Int))
         (=>
            (INV_REC_f__1 n$1_0_old _$1_0)
            (let
               ((result$1 _$1_0))
               (INV_REC_triangle__1 n$1_0_old result$1))))))
(assert
   (forall
      ((n$2_0_old Int))
      (forall
         ((_$2_0 Int))
         (=>
            (INV_REC_f__2 n$2_0_old 0 _$2_0)
            (let
               ((result$2 _$2_0))
               (INV_REC_triangle__2 n$2_0_old result$2))))))
; FORBIDDEN PATHS
; OFF BY N
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 0))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (<= n$2_0_old 0)))
                     (=>
                        _$2_0
                        (let
                           ((r.0$2_0 s$2_0_old))
                           (let
                              ((result$2 r.0$2_0))
                              (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2)))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 0))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (<= n$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((_$2_1 (- n$2_0_old 1))
                            (_$2_2 (+ n$2_0_old s$2_0_old)))
                           (let
                              ((_$2_3 (> _$2_2 15)))
                              (=>
                                 _$2_3
                                 (let
                                    ((_$2_4 (- _$2_2 32)))
                                    (let
                                       ((x.1$2_0 _$2_4))
                                       (forall
                                          ((_$2_7 Int))
                                          (=>
                                             (INV_REC_f__2 _$2_1 x.1$2_0 _$2_7)
                                             (let
                                                ((x.1$2_0 _$2_4)
                                                 (r.0$2_0 _$2_7))
                                                (let
                                                   ((result$2 r.0$2_0))
                                                   (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 0))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (<= n$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((_$2_1 (- n$2_0_old 1))
                            (_$2_2 (+ n$2_0_old s$2_0_old)))
                           (let
                              ((_$2_3 (> _$2_2 15)))
                              (=>
                                 (not _$2_3)
                                 (let
                                    ((_$2_5 (< _$2_2 (- 16))))
                                    (=>
                                       _$2_5
                                       (let
                                          ((_$2_6 (+ _$2_2 32)))
                                          (let
                                             ((x.0$2_0 _$2_6))
                                             (let
                                                ((x.1$2_0 x.0$2_0))
                                                (forall
                                                   ((_$2_7 Int))
                                                   (=>
                                                      (INV_REC_f__2 _$2_1 x.1$2_0 _$2_7)
                                                      (let
                                                         ((x.1$2_0 x.0$2_0)
                                                          (r.0$2_0 _$2_7))
                                                         (let
                                                            ((result$2 r.0$2_0))
                                                            (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((r.0$1_0 0))
                  (let
                     ((result$1 r.0$1_0)
                      (_$2_0 (<= n$2_0_old 0)))
                     (=>
                        (not _$2_0)
                        (let
                           ((_$2_1 (- n$2_0_old 1))
                            (_$2_2 (+ n$2_0_old s$2_0_old)))
                           (let
                              ((_$2_3 (> _$2_2 15)))
                              (=>
                                 (not _$2_3)
                                 (let
                                    ((_$2_5 (< _$2_2 (- 16))))
                                    (=>
                                       (not _$2_5)
                                       (let
                                          ((x.0$2_0 _$2_2))
                                          (let
                                             ((x.1$2_0 x.0$2_0))
                                             (forall
                                                ((_$2_7 Int))
                                                (=>
                                                   (INV_REC_f__2 _$2_1 x.1$2_0 _$2_7)
                                                   (let
                                                      ((x.1$2_0 x.0$2_0)
                                                       (r.0$2_0 _$2_7))
                                                      (let
                                                         ((result$2 r.0$2_0))
                                                         (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     _$2_0
                     (let
                        ((r.0$2_0 s$2_0_old))
                        (let
                           ((result$2 r.0$2_0))
                           (forall
                              ((_$1_2 Int))
                              (=>
                                 (INV_REC_f__1 _$1_1 _$1_2)
                                 (let
                                    ((_$1_1 (- n$1_0_old 1))
                                     (_$1_3 (+ _$1_2 n$1_0_old)))
                                    (let
                                       ((_$1_4 (> _$1_3 15)))
                                       (=>
                                          _$1_4
                                          (let
                                             ((_$1_5 (- _$1_3 32)))
                                             (let
                                                ((x.1$1_0 _$1_5))
                                                (let
                                                   ((r.0$1_0 x.1$1_0))
                                                   (let
                                                      ((result$1 r.0$1_0))
                                                      (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2)))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (- n$2_0_old 1))
                         (_$2_2 (+ n$2_0_old s$2_0_old)))
                        (let
                           ((_$2_3 (> _$2_2 15)))
                           (=>
                              _$2_3
                              (let
                                 ((_$2_4 (- _$2_2 32)))
                                 (let
                                    ((x.1$2_0 _$2_4))
                                    (and
                                       (INV_REC_f_PRE _$1_1 _$2_1 x.1$2_0)
                                       (forall
                                          ((_$1_2 Int)
                                           (_$2_7 Int))
                                          (=>
                                             (INV_REC_f _$1_1 _$2_1 x.1$2_0 _$1_2 _$2_7)
                                             (let
                                                ((_$1_1 (- n$1_0_old 1))
                                                 (_$1_3 (+ _$1_2 n$1_0_old)))
                                                (let
                                                   ((_$1_4 (> _$1_3 15)))
                                                   (=>
                                                      _$1_4
                                                      (let
                                                         ((_$1_5 (- _$1_3 32)))
                                                         (let
                                                            ((x.1$1_0 _$1_5))
                                                            (let
                                                               ((r.0$1_0 x.1$1_0))
                                                               (let
                                                                  ((result$1 r.0$1_0)
                                                                   (x.1$2_0 _$2_4)
                                                                   (r.0$2_0 _$2_7))
                                                                  (let
                                                                     ((result$2 r.0$2_0))
                                                                     (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (- n$2_0_old 1))
                         (_$2_2 (+ n$2_0_old s$2_0_old)))
                        (let
                           ((_$2_3 (> _$2_2 15)))
                           (=>
                              (not _$2_3)
                              (let
                                 ((_$2_5 (< _$2_2 (- 16))))
                                 (=>
                                    _$2_5
                                    (let
                                       ((_$2_6 (+ _$2_2 32)))
                                       (let
                                          ((x.0$2_0 _$2_6))
                                          (let
                                             ((x.1$2_0 x.0$2_0))
                                             (and
                                                (INV_REC_f_PRE _$1_1 _$2_1 x.1$2_0)
                                                (forall
                                                   ((_$1_2 Int)
                                                    (_$2_7 Int))
                                                   (=>
                                                      (INV_REC_f _$1_1 _$2_1 x.1$2_0 _$1_2 _$2_7)
                                                      (let
                                                         ((_$1_1 (- n$1_0_old 1))
                                                          (_$1_3 (+ _$1_2 n$1_0_old)))
                                                         (let
                                                            ((_$1_4 (> _$1_3 15)))
                                                            (=>
                                                               _$1_4
                                                               (let
                                                                  ((_$1_5 (- _$1_3 32)))
                                                                  (let
                                                                     ((x.1$1_0 _$1_5))
                                                                     (let
                                                                        ((r.0$1_0 x.1$1_0))
                                                                        (let
                                                                           ((result$1 r.0$1_0)
                                                                            (x.1$2_0 x.0$2_0)
                                                                            (r.0$2_0 _$2_7))
                                                                           (let
                                                                              ((result$2 r.0$2_0))
                                                                              (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (- n$2_0_old 1))
                         (_$2_2 (+ n$2_0_old s$2_0_old)))
                        (let
                           ((_$2_3 (> _$2_2 15)))
                           (=>
                              (not _$2_3)
                              (let
                                 ((_$2_5 (< _$2_2 (- 16))))
                                 (=>
                                    (not _$2_5)
                                    (let
                                       ((x.0$2_0 _$2_2))
                                       (let
                                          ((x.1$2_0 x.0$2_0))
                                          (and
                                             (INV_REC_f_PRE _$1_1 _$2_1 x.1$2_0)
                                             (forall
                                                ((_$1_2 Int)
                                                 (_$2_7 Int))
                                                (=>
                                                   (INV_REC_f _$1_1 _$2_1 x.1$2_0 _$1_2 _$2_7)
                                                   (let
                                                      ((_$1_1 (- n$1_0_old 1))
                                                       (_$1_3 (+ _$1_2 n$1_0_old)))
                                                      (let
                                                         ((_$1_4 (> _$1_3 15)))
                                                         (=>
                                                            _$1_4
                                                            (let
                                                               ((_$1_5 (- _$1_3 32)))
                                                               (let
                                                                  ((x.1$1_0 _$1_5))
                                                                  (let
                                                                     ((r.0$1_0 x.1$1_0))
                                                                     (let
                                                                        ((result$1 r.0$1_0)
                                                                         (x.1$2_0 x.0$2_0)
                                                                         (r.0$2_0 _$2_7))
                                                                        (let
                                                                           ((result$2 r.0$2_0))
                                                                           (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2))))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     _$2_0
                     (let
                        ((r.0$2_0 s$2_0_old))
                        (let
                           ((result$2 r.0$2_0))
                           (forall
                              ((_$1_2 Int))
                              (=>
                                 (INV_REC_f__1 _$1_1 _$1_2)
                                 (let
                                    ((_$1_1 (- n$1_0_old 1))
                                     (_$1_3 (+ _$1_2 n$1_0_old)))
                                    (let
                                       ((_$1_4 (> _$1_3 15)))
                                       (=>
                                          (not _$1_4)
                                          (let
                                             ((_$1_6 (< _$1_3 (- 16))))
                                             (=>
                                                _$1_6
                                                (let
                                                   ((_$1_7 (+ _$1_3 32)))
                                                   (let
                                                      ((x.0$1_0 _$1_7))
                                                      (let
                                                         ((x.1$1_0 x.0$1_0))
                                                         (let
                                                            ((r.0$1_0 x.1$1_0))
                                                            (let
                                                               ((result$1 r.0$1_0))
                                                               (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (- n$2_0_old 1))
                         (_$2_2 (+ n$2_0_old s$2_0_old)))
                        (let
                           ((_$2_3 (> _$2_2 15)))
                           (=>
                              _$2_3
                              (let
                                 ((_$2_4 (- _$2_2 32)))
                                 (let
                                    ((x.1$2_0 _$2_4))
                                    (and
                                       (INV_REC_f_PRE _$1_1 _$2_1 x.1$2_0)
                                       (forall
                                          ((_$1_2 Int)
                                           (_$2_7 Int))
                                          (=>
                                             (INV_REC_f _$1_1 _$2_1 x.1$2_0 _$1_2 _$2_7)
                                             (let
                                                ((_$1_1 (- n$1_0_old 1))
                                                 (_$1_3 (+ _$1_2 n$1_0_old)))
                                                (let
                                                   ((_$1_4 (> _$1_3 15)))
                                                   (=>
                                                      (not _$1_4)
                                                      (let
                                                         ((_$1_6 (< _$1_3 (- 16))))
                                                         (=>
                                                            _$1_6
                                                            (let
                                                               ((_$1_7 (+ _$1_3 32)))
                                                               (let
                                                                  ((x.0$1_0 _$1_7))
                                                                  (let
                                                                     ((x.1$1_0 x.0$1_0))
                                                                     (let
                                                                        ((r.0$1_0 x.1$1_0))
                                                                        (let
                                                                           ((result$1 r.0$1_0)
                                                                            (x.1$2_0 _$2_4)
                                                                            (r.0$2_0 _$2_7))
                                                                           (let
                                                                              ((result$2 r.0$2_0))
                                                                              (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (- n$2_0_old 1))
                         (_$2_2 (+ n$2_0_old s$2_0_old)))
                        (let
                           ((_$2_3 (> _$2_2 15)))
                           (=>
                              (not _$2_3)
                              (let
                                 ((_$2_5 (< _$2_2 (- 16))))
                                 (=>
                                    _$2_5
                                    (let
                                       ((_$2_6 (+ _$2_2 32)))
                                       (let
                                          ((x.0$2_0 _$2_6))
                                          (let
                                             ((x.1$2_0 x.0$2_0))
                                             (and
                                                (INV_REC_f_PRE _$1_1 _$2_1 x.1$2_0)
                                                (forall
                                                   ((_$1_2 Int)
                                                    (_$2_7 Int))
                                                   (=>
                                                      (INV_REC_f _$1_1 _$2_1 x.1$2_0 _$1_2 _$2_7)
                                                      (let
                                                         ((_$1_1 (- n$1_0_old 1))
                                                          (_$1_3 (+ _$1_2 n$1_0_old)))
                                                         (let
                                                            ((_$1_4 (> _$1_3 15)))
                                                            (=>
                                                               (not _$1_4)
                                                               (let
                                                                  ((_$1_6 (< _$1_3 (- 16))))
                                                                  (=>
                                                                     _$1_6
                                                                     (let
                                                                        ((_$1_7 (+ _$1_3 32)))
                                                                        (let
                                                                           ((x.0$1_0 _$1_7))
                                                                           (let
                                                                              ((x.1$1_0 x.0$1_0))
                                                                              (let
                                                                                 ((r.0$1_0 x.1$1_0))
                                                                                 (let
                                                                                    ((result$1 r.0$1_0)
                                                                                     (x.1$2_0 x.0$2_0)
                                                                                     (r.0$2_0 _$2_7))
                                                                                    (let
                                                                                       ((result$2 r.0$2_0))
                                                                                       (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (- n$2_0_old 1))
                         (_$2_2 (+ n$2_0_old s$2_0_old)))
                        (let
                           ((_$2_3 (> _$2_2 15)))
                           (=>
                              (not _$2_3)
                              (let
                                 ((_$2_5 (< _$2_2 (- 16))))
                                 (=>
                                    (not _$2_5)
                                    (let
                                       ((x.0$2_0 _$2_2))
                                       (let
                                          ((x.1$2_0 x.0$2_0))
                                          (and
                                             (INV_REC_f_PRE _$1_1 _$2_1 x.1$2_0)
                                             (forall
                                                ((_$1_2 Int)
                                                 (_$2_7 Int))
                                                (=>
                                                   (INV_REC_f _$1_1 _$2_1 x.1$2_0 _$1_2 _$2_7)
                                                   (let
                                                      ((_$1_1 (- n$1_0_old 1))
                                                       (_$1_3 (+ _$1_2 n$1_0_old)))
                                                      (let
                                                         ((_$1_4 (> _$1_3 15)))
                                                         (=>
                                                            (not _$1_4)
                                                            (let
                                                               ((_$1_6 (< _$1_3 (- 16))))
                                                               (=>
                                                                  _$1_6
                                                                  (let
                                                                     ((_$1_7 (+ _$1_3 32)))
                                                                     (let
                                                                        ((x.0$1_0 _$1_7))
                                                                        (let
                                                                           ((x.1$1_0 x.0$1_0))
                                                                           (let
                                                                              ((r.0$1_0 x.1$1_0))
                                                                              (let
                                                                                 ((result$1 r.0$1_0)
                                                                                  (x.1$2_0 x.0$2_0)
                                                                                  (r.0$2_0 _$2_7))
                                                                                 (let
                                                                                    ((result$2 r.0$2_0))
                                                                                    (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     _$2_0
                     (let
                        ((r.0$2_0 s$2_0_old))
                        (let
                           ((result$2 r.0$2_0))
                           (forall
                              ((_$1_2 Int))
                              (=>
                                 (INV_REC_f__1 _$1_1 _$1_2)
                                 (let
                                    ((_$1_1 (- n$1_0_old 1))
                                     (_$1_3 (+ _$1_2 n$1_0_old)))
                                    (let
                                       ((_$1_4 (> _$1_3 15)))
                                       (=>
                                          (not _$1_4)
                                          (let
                                             ((_$1_6 (< _$1_3 (- 16))))
                                             (=>
                                                (not _$1_6)
                                                (let
                                                   ((x.0$1_0 _$1_3))
                                                   (let
                                                      ((x.1$1_0 x.0$1_0))
                                                      (let
                                                         ((r.0$1_0 x.1$1_0))
                                                         (let
                                                            ((result$1 r.0$1_0))
                                                            (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2)))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (- n$2_0_old 1))
                         (_$2_2 (+ n$2_0_old s$2_0_old)))
                        (let
                           ((_$2_3 (> _$2_2 15)))
                           (=>
                              _$2_3
                              (let
                                 ((_$2_4 (- _$2_2 32)))
                                 (let
                                    ((x.1$2_0 _$2_4))
                                    (and
                                       (INV_REC_f_PRE _$1_1 _$2_1 x.1$2_0)
                                       (forall
                                          ((_$1_2 Int)
                                           (_$2_7 Int))
                                          (=>
                                             (INV_REC_f _$1_1 _$2_1 x.1$2_0 _$1_2 _$2_7)
                                             (let
                                                ((_$1_1 (- n$1_0_old 1))
                                                 (_$1_3 (+ _$1_2 n$1_0_old)))
                                                (let
                                                   ((_$1_4 (> _$1_3 15)))
                                                   (=>
                                                      (not _$1_4)
                                                      (let
                                                         ((_$1_6 (< _$1_3 (- 16))))
                                                         (=>
                                                            (not _$1_6)
                                                            (let
                                                               ((x.0$1_0 _$1_3))
                                                               (let
                                                                  ((x.1$1_0 x.0$1_0))
                                                                  (let
                                                                     ((r.0$1_0 x.1$1_0))
                                                                     (let
                                                                        ((result$1 r.0$1_0)
                                                                         (x.1$2_0 _$2_4)
                                                                         (r.0$2_0 _$2_7))
                                                                        (let
                                                                           ((result$2 r.0$2_0))
                                                                           (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2))))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (- n$2_0_old 1))
                         (_$2_2 (+ n$2_0_old s$2_0_old)))
                        (let
                           ((_$2_3 (> _$2_2 15)))
                           (=>
                              (not _$2_3)
                              (let
                                 ((_$2_5 (< _$2_2 (- 16))))
                                 (=>
                                    _$2_5
                                    (let
                                       ((_$2_6 (+ _$2_2 32)))
                                       (let
                                          ((x.0$2_0 _$2_6))
                                          (let
                                             ((x.1$2_0 x.0$2_0))
                                             (and
                                                (INV_REC_f_PRE _$1_1 _$2_1 x.1$2_0)
                                                (forall
                                                   ((_$1_2 Int)
                                                    (_$2_7 Int))
                                                   (=>
                                                      (INV_REC_f _$1_1 _$2_1 x.1$2_0 _$1_2 _$2_7)
                                                      (let
                                                         ((_$1_1 (- n$1_0_old 1))
                                                          (_$1_3 (+ _$1_2 n$1_0_old)))
                                                         (let
                                                            ((_$1_4 (> _$1_3 15)))
                                                            (=>
                                                               (not _$1_4)
                                                               (let
                                                                  ((_$1_6 (< _$1_3 (- 16))))
                                                                  (=>
                                                                     (not _$1_6)
                                                                     (let
                                                                        ((x.0$1_0 _$1_3))
                                                                        (let
                                                                           ((x.1$1_0 x.0$1_0))
                                                                           (let
                                                                              ((r.0$1_0 x.1$1_0))
                                                                              (let
                                                                                 ((result$1 r.0$1_0)
                                                                                  (x.1$2_0 x.0$2_0)
                                                                                  (r.0$2_0 _$2_7))
                                                                                 (let
                                                                                    ((result$2 r.0$2_0))
                                                                                    (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int)
       (s$2_0_old Int))
      (=>
         (INV_REC_f_PRE n$1_0_old n$2_0_old s$2_0_old)
         (let
            ((_$1_0 (<= n$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_1 (- n$1_0_old 1))
                   (_$2_0 (<= n$2_0_old 0)))
                  (=>
                     (not _$2_0)
                     (let
                        ((_$2_1 (- n$2_0_old 1))
                         (_$2_2 (+ n$2_0_old s$2_0_old)))
                        (let
                           ((_$2_3 (> _$2_2 15)))
                           (=>
                              (not _$2_3)
                              (let
                                 ((_$2_5 (< _$2_2 (- 16))))
                                 (=>
                                    (not _$2_5)
                                    (let
                                       ((x.0$2_0 _$2_2))
                                       (let
                                          ((x.1$2_0 x.0$2_0))
                                          (and
                                             (INV_REC_f_PRE _$1_1 _$2_1 x.1$2_0)
                                             (forall
                                                ((_$1_2 Int)
                                                 (_$2_7 Int))
                                                (=>
                                                   (INV_REC_f _$1_1 _$2_1 x.1$2_0 _$1_2 _$2_7)
                                                   (let
                                                      ((_$1_1 (- n$1_0_old 1))
                                                       (_$1_3 (+ _$1_2 n$1_0_old)))
                                                      (let
                                                         ((_$1_4 (> _$1_3 15)))
                                                         (=>
                                                            (not _$1_4)
                                                            (let
                                                               ((_$1_6 (< _$1_3 (- 16))))
                                                               (=>
                                                                  (not _$1_6)
                                                                  (let
                                                                     ((x.0$1_0 _$1_3))
                                                                     (let
                                                                        ((x.1$1_0 x.0$1_0))
                                                                        (let
                                                                           ((r.0$1_0 x.1$1_0))
                                                                           (let
                                                                              ((result$1 r.0$1_0)
                                                                               (x.1$2_0 x.0$2_0)
                                                                               (r.0$2_0 _$2_7))
                                                                              (let
                                                                                 ((result$2 r.0$2_0))
                                                                                 (INV_REC_f n$1_0_old n$2_0_old s$2_0_old result$1 result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (let
         ((_$1_0 (<= n$1_0_old 0)))
         (=>
            _$1_0
            (let
               ((r.0$1_0 0))
               (let
                  ((result$1 r.0$1_0))
                  (INV_REC_f__1 n$1_0_old result$1)))))))
(assert
   (forall
      ((n$1_0_old Int))
      (let
         ((_$1_0 (<= n$1_0_old 0)))
         (=>
            (not _$1_0)
            (let
               ((_$1_1 (- n$1_0_old 1)))
               (forall
                  ((_$1_2 Int))
                  (=>
                     (INV_REC_f__1 _$1_1 _$1_2)
                     (let
                        ((_$1_1 (- n$1_0_old 1))
                         (_$1_3 (+ _$1_2 n$1_0_old)))
                        (let
                           ((_$1_4 (> _$1_3 15)))
                           (=>
                              _$1_4
                              (let
                                 ((_$1_5 (- _$1_3 32)))
                                 (let
                                    ((x.1$1_0 _$1_5))
                                    (let
                                       ((r.0$1_0 x.1$1_0))
                                       (let
                                          ((result$1 r.0$1_0))
                                          (INV_REC_f__1 n$1_0_old result$1)))))))))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (let
         ((_$1_0 (<= n$1_0_old 0)))
         (=>
            (not _$1_0)
            (let
               ((_$1_1 (- n$1_0_old 1)))
               (forall
                  ((_$1_2 Int))
                  (=>
                     (INV_REC_f__1 _$1_1 _$1_2)
                     (let
                        ((_$1_1 (- n$1_0_old 1))
                         (_$1_3 (+ _$1_2 n$1_0_old)))
                        (let
                           ((_$1_4 (> _$1_3 15)))
                           (=>
                              (not _$1_4)
                              (let
                                 ((_$1_6 (< _$1_3 (- 16))))
                                 (=>
                                    _$1_6
                                    (let
                                       ((_$1_7 (+ _$1_3 32)))
                                       (let
                                          ((x.0$1_0 _$1_7))
                                          (let
                                             ((x.1$1_0 x.0$1_0))
                                             (let
                                                ((r.0$1_0 x.1$1_0))
                                                (let
                                                   ((result$1 r.0$1_0))
                                                   (INV_REC_f__1 n$1_0_old result$1))))))))))))))))))
(assert
   (forall
      ((n$1_0_old Int))
      (let
         ((_$1_0 (<= n$1_0_old 0)))
         (=>
            (not _$1_0)
            (let
               ((_$1_1 (- n$1_0_old 1)))
               (forall
                  ((_$1_2 Int))
                  (=>
                     (INV_REC_f__1 _$1_1 _$1_2)
                     (let
                        ((_$1_1 (- n$1_0_old 1))
                         (_$1_3 (+ _$1_2 n$1_0_old)))
                        (let
                           ((_$1_4 (> _$1_3 15)))
                           (=>
                              (not _$1_4)
                              (let
                                 ((_$1_6 (< _$1_3 (- 16))))
                                 (=>
                                    (not _$1_6)
                                    (let
                                       ((x.0$1_0 _$1_3))
                                       (let
                                          ((x.1$1_0 x.0$1_0))
                                          (let
                                             ((r.0$1_0 x.1$1_0))
                                             (let
                                                ((result$1 r.0$1_0))
                                                (INV_REC_f__1 n$1_0_old result$1)))))))))))))))))
(assert
   (forall
      ((n$2_0_old Int)
       (s$2_0_old Int))
      (let
         ((_$2_0 (<= n$2_0_old 0)))
         (=>
            _$2_0
            (let
               ((r.0$2_0 s$2_0_old))
               (let
                  ((result$2 r.0$2_0))
                  (INV_REC_f__2 n$2_0_old s$2_0_old result$2)))))))
(assert
   (forall
      ((n$2_0_old Int)
       (s$2_0_old Int))
      (let
         ((_$2_0 (<= n$2_0_old 0)))
         (=>
            (not _$2_0)
            (let
               ((_$2_1 (- n$2_0_old 1))
                (_$2_2 (+ n$2_0_old s$2_0_old)))
               (let
                  ((_$2_3 (> _$2_2 15)))
                  (=>
                     _$2_3
                     (let
                        ((_$2_4 (- _$2_2 32)))
                        (let
                           ((x.1$2_0 _$2_4))
                           (forall
                              ((_$2_7 Int))
                              (=>
                                 (INV_REC_f__2 _$2_1 x.1$2_0 _$2_7)
                                 (let
                                    ((x.1$2_0 _$2_4)
                                     (r.0$2_0 _$2_7))
                                    (let
                                       ((result$2 r.0$2_0))
                                       (INV_REC_f__2 n$2_0_old s$2_0_old result$2))))))))))))))
(assert
   (forall
      ((n$2_0_old Int)
       (s$2_0_old Int))
      (let
         ((_$2_0 (<= n$2_0_old 0)))
         (=>
            (not _$2_0)
            (let
               ((_$2_1 (- n$2_0_old 1))
                (_$2_2 (+ n$2_0_old s$2_0_old)))
               (let
                  ((_$2_3 (> _$2_2 15)))
                  (=>
                     (not _$2_3)
                     (let
                        ((_$2_5 (< _$2_2 (- 16))))
                        (=>
                           _$2_5
                           (let
                              ((_$2_6 (+ _$2_2 32)))
                              (let
                                 ((x.0$2_0 _$2_6))
                                 (let
                                    ((x.1$2_0 x.0$2_0))
                                    (forall
                                       ((_$2_7 Int))
                                       (=>
                                          (INV_REC_f__2 _$2_1 x.1$2_0 _$2_7)
                                          (let
                                             ((x.1$2_0 x.0$2_0)
                                              (r.0$2_0 _$2_7))
                                             (let
                                                ((result$2 r.0$2_0))
                                                (INV_REC_f__2 n$2_0_old s$2_0_old result$2)))))))))))))))))
(assert
   (forall
      ((n$2_0_old Int)
       (s$2_0_old Int))
      (let
         ((_$2_0 (<= n$2_0_old 0)))
         (=>
            (not _$2_0)
            (let
               ((_$2_1 (- n$2_0_old 1))
                (_$2_2 (+ n$2_0_old s$2_0_old)))
               (let
                  ((_$2_3 (> _$2_2 15)))
                  (=>
                     (not _$2_3)
                     (let
                        ((_$2_5 (< _$2_2 (- 16))))
                        (=>
                           (not _$2_5)
                           (let
                              ((x.0$2_0 _$2_2))
                              (let
                                 ((x.1$2_0 x.0$2_0))
                                 (forall
                                    ((_$2_7 Int))
                                    (=>
                                       (INV_REC_f__2 _$2_1 x.1$2_0 _$2_7)
                                       (let
                                          ((x.1$2_0 x.0$2_0)
                                           (r.0$2_0 _$2_7))
                                          (let
                                             ((result$2 r.0$2_0))
                                             (INV_REC_f__2 n$2_0_old s$2_0_old result$2))))))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(check-sat)
(get-model)
