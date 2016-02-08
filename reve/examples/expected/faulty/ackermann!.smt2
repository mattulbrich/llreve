(set-logic HORN)
(define-fun
   IN_INV
   ((m$1_0 Int)
    (n$1_0 Int)
    (m$2_0 Int)
    (n$2_0 Int))
   Bool
   (and
      (= m$1_0 m$2_0)
      (= n$1_0 n$2_0)))
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
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_2 (- m$2_0_old 1)))
                                    (and
                                       (INV_REC_f__2_PRE _$2_2 1)
                                       (forall
                                          ((_$2_3 Int))
                                          (=>
                                             (INV_REC_f__2 _$2_2 1 _$2_3)
                                             (let
                                                ((r.1$2_0 _$2_3))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (OUT_INV
                                                      result$1
                                                      result$2))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       _$2_4
                                       (let
                                          ((_$2_5 (+ n$2_0_old 1)))
                                          (let
                                             ((r.0$2_0 _$2_5))
                                             (let
                                                ((r.1$2_0 r.0$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (OUT_INV
                                                      result$1
                                                      result$2))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       (not _$2_4)
                                       (let
                                          ((_$2_6 (- n$2_0_old 1)))
                                          (and
                                             (INV_REC_f__2_PRE m$2_0_old _$2_6)
                                             (forall
                                                ((_$2_7 Int))
                                                (=>
                                                   (INV_REC_f__2 m$2_0_old _$2_6 _$2_7)
                                                   (let
                                                      ((_$2_8 (- m$2_0_old 1)))
                                                      (and
                                                         (INV_REC_f__2_PRE _$2_8 _$2_7)
                                                         (forall
                                                            ((_$2_9 Int))
                                                            (=>
                                                               (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                                               (let
                                                                  ((r.0$2_0 _$2_9))
                                                                  (let
                                                                     ((r.1$2_0 r.0$2_0))
                                                                     (let
                                                                        ((result$2 r.1$2_0))
                                                                        (OUT_INV
                                                                           result$1
                                                                           result$2)))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (= m$2_0_old 1)))
                              (=>
                                 _$2_4
                                 (let
                                    ((_$2_5 (+ n$2_0_old 1)))
                                    (let
                                       ((r.0$2_0 _$2_5))
                                       (let
                                          ((r.1$2_0 r.0$2_0))
                                          (let
                                             ((result$2 r.1$2_0))
                                             (OUT_INV
                                                result$1
                                                result$2))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (= m$2_0_old 1)))
                              (=>
                                 (not _$2_4)
                                 (let
                                    ((_$2_6 (- n$2_0_old 1)))
                                    (and
                                       (INV_REC_f__2_PRE m$2_0_old _$2_6)
                                       (forall
                                          ((_$2_7 Int))
                                          (=>
                                             (INV_REC_f__2 m$2_0_old _$2_6 _$2_7)
                                             (let
                                                ((_$2_8 (- m$2_0_old 1)))
                                                (and
                                                   (INV_REC_f__2_PRE _$2_8 _$2_7)
                                                   (forall
                                                      ((_$2_9 Int))
                                                      (=>
                                                         (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                                         (let
                                                            ((r.0$2_0 _$2_9))
                                                            (let
                                                               ((r.1$2_0 r.0$2_0))
                                                               (let
                                                                  ((result$2 r.1$2_0))
                                                                  (OUT_INV
                                                                     result$1
                                                                     result$2)))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       _$2_1
                                       (let
                                          ((_$2_2 (- m$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE _$1_4 1 _$2_2 1)
                                             (forall
                                                ((_$1_5 Int)
                                                 (_$2_3 Int))
                                                (=>
                                                   (INV_REC_f _$1_4 1 _$2_2 1 _$1_5 _$2_3)
                                                   (let
                                                      ((r.0$1_0 _$1_5))
                                                      (let
                                                         ((r.1$1_0 r.0$1_0))
                                                         (let
                                                            ((result$1 r.1$1_0)
                                                             (r.1$2_0 _$2_3))
                                                            (let
                                                               ((result$2 r.1$2_0))
                                                               (OUT_INV
                                                                  result$1
                                                                  result$2))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_4 (= m$2_0_old 1)))
                                          (=>
                                             _$2_4
                                             (let
                                                ((_$2_5 (+ n$2_0_old 1)))
                                                (let
                                                   ((r.0$2_0 _$2_5))
                                                   (let
                                                      ((r.1$2_0 r.0$2_0))
                                                      (let
                                                         ((result$2 r.1$2_0))
                                                         (and
                                                            (INV_REC_f__1_PRE _$1_4 1)
                                                            (forall
                                                               ((_$1_5 Int))
                                                               (=>
                                                                  (INV_REC_f__1 _$1_4 1 _$1_5)
                                                                  (let
                                                                     ((r.0$1_0 _$1_5))
                                                                     (let
                                                                        ((r.1$1_0 r.0$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0))
                                                                           (OUT_INV
                                                                              result$1
                                                                              result$2))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_4 (= m$2_0_old 1)))
                                          (=>
                                             (not _$2_4)
                                             (let
                                                ((_$2_6 (- n$2_0_old 1)))
                                                (and
                                                   (INV_REC_f_PRE _$1_4 1 m$2_0_old _$2_6)
                                                   (forall
                                                      ((_$1_5 Int)
                                                       (_$2_7 Int))
                                                      (=>
                                                         (INV_REC_f _$1_4 1 m$2_0_old _$2_6 _$1_5 _$2_7)
                                                         (let
                                                            ((r.0$1_0 _$1_5))
                                                            (let
                                                               ((r.1$1_0 r.0$1_0))
                                                               (let
                                                                  ((result$1 r.1$1_0)
                                                                   (_$2_8 (- m$2_0_old 1)))
                                                                  (and
                                                                     (INV_REC_f__2_PRE _$2_8 _$2_7)
                                                                     (forall
                                                                        ((_$2_9 Int))
                                                                        (=>
                                                                           (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                                                           (let
                                                                              ((r.0$2_0 _$2_9))
                                                                              (let
                                                                                 ((r.1$2_0 r.0$2_0))
                                                                                 (let
                                                                                    ((result$2 r.1$2_0))
                                                                                    (OUT_INV
                                                                                       result$1
                                                                                       result$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       _$2_4
                                       (let
                                          ((_$2_5 (+ n$2_0_old 1)))
                                          (let
                                             ((r.0$2_0 _$2_5))
                                             (let
                                                ((r.1$2_0 r.0$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (and
                                                      (INV_REC_f__1_PRE _$1_4 1)
                                                      (forall
                                                         ((_$1_5 Int))
                                                         (=>
                                                            (INV_REC_f__1 _$1_4 1 _$1_5)
                                                            (let
                                                               ((r.0$1_0 _$1_5))
                                                               (let
                                                                  ((r.1$1_0 r.0$1_0))
                                                                  (let
                                                                     ((result$1 r.1$1_0))
                                                                     (OUT_INV
                                                                        result$1
                                                                        result$2))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       (not _$2_4)
                                       (let
                                          ((_$2_6 (- n$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE _$1_4 1 m$2_0_old _$2_6)
                                             (forall
                                                ((_$1_5 Int)
                                                 (_$2_7 Int))
                                                (=>
                                                   (INV_REC_f _$1_4 1 m$2_0_old _$2_6 _$1_5 _$2_7)
                                                   (let
                                                      ((r.0$1_0 _$1_5))
                                                      (let
                                                         ((r.1$1_0 r.0$1_0))
                                                         (let
                                                            ((result$1 r.1$1_0)
                                                             (_$2_8 (- m$2_0_old 1)))
                                                            (and
                                                               (INV_REC_f__2_PRE _$2_8 _$2_7)
                                                               (forall
                                                                  ((_$2_9 Int))
                                                                  (=>
                                                                     (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                                                     (let
                                                                        ((r.0$2_0 _$2_9))
                                                                        (let
                                                                           ((r.1$2_0 r.0$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (OUT_INV
                                                                                 result$1
                                                                                 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       _$2_1
                                       (let
                                          ((_$2_2 (- m$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE m$1_0_old _$1_6 _$2_2 1)
                                             (forall
                                                ((_$1_7 Int)
                                                 (_$2_3 Int))
                                                (=>
                                                   (INV_REC_f m$1_0_old _$1_6 _$2_2 1 _$1_7 _$2_3)
                                                   (let
                                                      ((_$1_8 (- m$1_0_old 1))
                                                       (r.1$2_0 _$2_3))
                                                      (let
                                                         ((result$2 r.1$2_0))
                                                         (and
                                                            (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                            (forall
                                                               ((_$1_9 Int))
                                                               (=>
                                                                  (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                  (let
                                                                     ((r.0$1_0 _$1_9))
                                                                     (let
                                                                        ((r.1$1_0 r.0$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0))
                                                                           (OUT_INV
                                                                              result$1
                                                                              result$2))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_4 (= m$2_0_old 1)))
                                          (=>
                                             _$2_4
                                             (let
                                                ((_$2_5 (+ n$2_0_old 1)))
                                                (let
                                                   ((r.0$2_0 _$2_5))
                                                   (let
                                                      ((r.1$2_0 r.0$2_0))
                                                      (let
                                                         ((result$2 r.1$2_0))
                                                         (and
                                                            (INV_REC_f__1_PRE m$1_0_old _$1_6)
                                                            (forall
                                                               ((_$1_7 Int))
                                                               (=>
                                                                  (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                                                  (let
                                                                     ((_$1_8 (- m$1_0_old 1)))
                                                                     (and
                                                                        (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                                        (forall
                                                                           ((_$1_9 Int))
                                                                           (=>
                                                                              (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                              (let
                                                                                 ((r.0$1_0 _$1_9))
                                                                                 (let
                                                                                    ((r.1$1_0 r.0$1_0))
                                                                                    (let
                                                                                       ((result$1 r.1$1_0))
                                                                                       (OUT_INV
                                                                                          result$1
                                                                                          result$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_4 (= m$2_0_old 1)))
                                          (=>
                                             (not _$2_4)
                                             (let
                                                ((_$2_6 (- n$2_0_old 1)))
                                                (and
                                                   (INV_REC_f_PRE m$1_0_old _$1_6 m$2_0_old _$2_6)
                                                   (forall
                                                      ((_$1_7 Int)
                                                       (_$2_7 Int))
                                                      (=>
                                                         (INV_REC_f m$1_0_old _$1_6 m$2_0_old _$2_6 _$1_7 _$2_7)
                                                         (let
                                                            ((_$1_8 (- m$1_0_old 1))
                                                             (_$2_8 (- m$2_0_old 1)))
                                                            (and
                                                               (INV_REC_f_PRE _$1_8 _$1_7 _$2_8 _$2_7)
                                                               (forall
                                                                  ((_$1_9 Int)
                                                                   (_$2_9 Int))
                                                                  (=>
                                                                     (INV_REC_f _$1_8 _$1_7 _$2_8 _$2_7 _$1_9 _$2_9)
                                                                     (let
                                                                        ((r.0$1_0 _$1_9))
                                                                        (let
                                                                           ((r.1$1_0 r.0$1_0))
                                                                           (let
                                                                              ((result$1 r.1$1_0)
                                                                               (r.0$2_0 _$2_9))
                                                                              (let
                                                                                 ((r.1$2_0 r.0$2_0))
                                                                                 (let
                                                                                    ((result$2 r.1$2_0))
                                                                                    (OUT_INV
                                                                                       result$1
                                                                                       result$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       _$2_4
                                       (let
                                          ((_$2_5 (+ n$2_0_old 1)))
                                          (let
                                             ((r.0$2_0 _$2_5))
                                             (let
                                                ((r.1$2_0 r.0$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (and
                                                      (INV_REC_f__1_PRE m$1_0_old _$1_6)
                                                      (forall
                                                         ((_$1_7 Int))
                                                         (=>
                                                            (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                                            (let
                                                               ((_$1_8 (- m$1_0_old 1)))
                                                               (and
                                                                  (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                                  (forall
                                                                     ((_$1_9 Int))
                                                                     (=>
                                                                        (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                        (let
                                                                           ((r.0$1_0 _$1_9))
                                                                           (let
                                                                              ((r.1$1_0 r.0$1_0))
                                                                              (let
                                                                                 ((result$1 r.1$1_0))
                                                                                 (OUT_INV
                                                                                    result$1
                                                                                    result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       (not _$2_4)
                                       (let
                                          ((_$2_6 (- n$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE m$1_0_old _$1_6 m$2_0_old _$2_6)
                                             (forall
                                                ((_$1_7 Int)
                                                 (_$2_7 Int))
                                                (=>
                                                   (INV_REC_f m$1_0_old _$1_6 m$2_0_old _$2_6 _$1_7 _$2_7)
                                                   (let
                                                      ((_$1_8 (- m$1_0_old 1))
                                                       (_$2_8 (- m$2_0_old 1)))
                                                      (and
                                                         (INV_REC_f_PRE _$1_8 _$1_7 _$2_8 _$2_7)
                                                         (forall
                                                            ((_$1_9 Int)
                                                             (_$2_9 Int))
                                                            (=>
                                                               (INV_REC_f _$1_8 _$1_7 _$2_8 _$2_7 _$1_9 _$2_9)
                                                               (let
                                                                  ((r.0$1_0 _$1_9))
                                                                  (let
                                                                     ((r.1$1_0 r.0$1_0))
                                                                     (let
                                                                        ((result$1 r.1$1_0)
                                                                         (r.0$2_0 _$2_9))
                                                                        (let
                                                                           ((r.1$2_0 r.0$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (OUT_INV
                                                                                 result$1
                                                                                 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_2 (- m$2_0_old 1)))
                                    (and
                                       (INV_REC_f_PRE m$1_0_old _$1_6 _$2_2 1)
                                       (forall
                                          ((_$1_7 Int)
                                           (_$2_3 Int))
                                          (=>
                                             (INV_REC_f m$1_0_old _$1_6 _$2_2 1 _$1_7 _$2_3)
                                             (let
                                                ((_$1_8 (- m$1_0_old 1))
                                                 (r.1$2_0 _$2_3))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (and
                                                      (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                      (forall
                                                         ((_$1_9 Int))
                                                         (=>
                                                            (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                            (let
                                                               ((r.0$1_0 _$1_9))
                                                               (let
                                                                  ((r.1$1_0 r.0$1_0))
                                                                  (let
                                                                     ((result$1 r.1$1_0))
                                                                     (OUT_INV
                                                                        result$1
                                                                        result$2))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       _$2_4
                                       (let
                                          ((_$2_5 (+ n$2_0_old 1)))
                                          (let
                                             ((r.0$2_0 _$2_5))
                                             (let
                                                ((r.1$2_0 r.0$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (and
                                                      (INV_REC_f__1_PRE m$1_0_old _$1_6)
                                                      (forall
                                                         ((_$1_7 Int))
                                                         (=>
                                                            (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                                            (let
                                                               ((_$1_8 (- m$1_0_old 1)))
                                                               (and
                                                                  (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                                  (forall
                                                                     ((_$1_9 Int))
                                                                     (=>
                                                                        (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                        (let
                                                                           ((r.0$1_0 _$1_9))
                                                                           (let
                                                                              ((r.1$1_0 r.0$1_0))
                                                                              (let
                                                                                 ((result$1 r.1$1_0))
                                                                                 (OUT_INV
                                                                                    result$1
                                                                                    result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       (not _$2_4)
                                       (let
                                          ((_$2_6 (- n$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE m$1_0_old _$1_6 m$2_0_old _$2_6)
                                             (forall
                                                ((_$1_7 Int)
                                                 (_$2_7 Int))
                                                (=>
                                                   (INV_REC_f m$1_0_old _$1_6 m$2_0_old _$2_6 _$1_7 _$2_7)
                                                   (let
                                                      ((_$1_8 (- m$1_0_old 1))
                                                       (_$2_8 (- m$2_0_old 1)))
                                                      (and
                                                         (INV_REC_f_PRE _$1_8 _$1_7 _$2_8 _$2_7)
                                                         (forall
                                                            ((_$1_9 Int)
                                                             (_$2_9 Int))
                                                            (=>
                                                               (INV_REC_f _$1_8 _$1_7 _$2_8 _$2_7 _$1_9 _$2_9)
                                                               (let
                                                                  ((r.0$1_0 _$1_9))
                                                                  (let
                                                                     ((r.1$1_0 r.0$1_0))
                                                                     (let
                                                                        ((result$1 r.1$1_0)
                                                                         (r.0$2_0 _$2_9))
                                                                        (let
                                                                           ((r.1$2_0 r.0$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (OUT_INV
                                                                                 result$1
                                                                                 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (= m$2_0_old 1)))
                              (=>
                                 _$2_4
                                 (let
                                    ((_$2_5 (+ n$2_0_old 1)))
                                    (let
                                       ((r.0$2_0 _$2_5))
                                       (let
                                          ((r.1$2_0 r.0$2_0))
                                          (let
                                             ((result$2 r.1$2_0))
                                             (and
                                                (INV_REC_f__1_PRE m$1_0_old _$1_6)
                                                (forall
                                                   ((_$1_7 Int))
                                                   (=>
                                                      (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                                      (let
                                                         ((_$1_8 (- m$1_0_old 1)))
                                                         (and
                                                            (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                            (forall
                                                               ((_$1_9 Int))
                                                               (=>
                                                                  (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                  (let
                                                                     ((r.0$1_0 _$1_9))
                                                                     (let
                                                                        ((r.1$1_0 r.0$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0))
                                                                           (OUT_INV
                                                                              result$1
                                                                              result$2))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV
            m$1_0_old
            n$1_0_old
            m$2_0_old
            n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (= m$2_0_old 1)))
                              (=>
                                 (not _$2_4)
                                 (let
                                    ((_$2_6 (- n$2_0_old 1)))
                                    (and
                                       (INV_REC_f_PRE m$1_0_old _$1_6 m$2_0_old _$2_6)
                                       (forall
                                          ((_$1_7 Int)
                                           (_$2_7 Int))
                                          (=>
                                             (INV_REC_f m$1_0_old _$1_6 m$2_0_old _$2_6 _$1_7 _$2_7)
                                             (let
                                                ((_$1_8 (- m$1_0_old 1))
                                                 (_$2_8 (- m$2_0_old 1)))
                                                (and
                                                   (INV_REC_f_PRE _$1_8 _$1_7 _$2_8 _$2_7)
                                                   (forall
                                                      ((_$1_9 Int)
                                                       (_$2_9 Int))
                                                      (=>
                                                         (INV_REC_f _$1_8 _$1_7 _$2_8 _$2_7 _$1_9 _$2_9)
                                                         (let
                                                            ((r.0$1_0 _$1_9))
                                                            (let
                                                               ((r.1$1_0 r.0$1_0))
                                                               (let
                                                                  ((result$1 r.1$1_0)
                                                                   (r.0$2_0 _$2_9))
                                                                  (let
                                                                     ((r.1$2_0 r.0$2_0))
                                                                     (let
                                                                        ((result$2 r.1$2_0))
                                                                        (OUT_INV
                                                                           result$1
                                                                           result$2)))))))))))))))))))))))))
; forbidden main
; offbyn main
; end
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_2 (- m$2_0_old 1)))
                                    (and
                                       (INV_REC_f__2_PRE _$2_2 1)
                                       (forall
                                          ((_$2_3 Int))
                                          (=>
                                             (INV_REC_f__2 _$2_2 1 _$2_3)
                                             (let
                                                ((r.1$2_0 _$2_3))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       _$2_4
                                       (let
                                          ((_$2_5 (+ n$2_0_old 1)))
                                          (let
                                             ((r.0$2_0 _$2_5))
                                             (let
                                                ((r.1$2_0 r.0$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       (not _$2_4)
                                       (let
                                          ((_$2_6 (- n$2_0_old 1)))
                                          (and
                                             (INV_REC_f__2_PRE m$2_0_old _$2_6)
                                             (forall
                                                ((_$2_7 Int))
                                                (=>
                                                   (INV_REC_f__2 m$2_0_old _$2_6 _$2_7)
                                                   (let
                                                      ((_$2_8 (- m$2_0_old 1)))
                                                      (and
                                                         (INV_REC_f__2_PRE _$2_8 _$2_7)
                                                         (forall
                                                            ((_$2_9 Int))
                                                            (=>
                                                               (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                                               (let
                                                                  ((r.0$2_0 _$2_9))
                                                                  (let
                                                                     ((r.1$2_0 r.0$2_0))
                                                                     (let
                                                                        ((result$2 r.1$2_0))
                                                                        (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (= m$2_0_old 1)))
                              (=>
                                 _$2_4
                                 (let
                                    ((_$2_5 (+ n$2_0_old 1)))
                                    (let
                                       ((r.0$2_0 _$2_5))
                                       (let
                                          ((r.1$2_0 r.0$2_0))
                                          (let
                                             ((result$2 r.1$2_0))
                                             (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0)
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (= m$2_0_old 1)))
                              (=>
                                 (not _$2_4)
                                 (let
                                    ((_$2_6 (- n$2_0_old 1)))
                                    (and
                                       (INV_REC_f__2_PRE m$2_0_old _$2_6)
                                       (forall
                                          ((_$2_7 Int))
                                          (=>
                                             (INV_REC_f__2 m$2_0_old _$2_6 _$2_7)
                                             (let
                                                ((_$2_8 (- m$2_0_old 1)))
                                                (and
                                                   (INV_REC_f__2_PRE _$2_8 _$2_7)
                                                   (forall
                                                      ((_$2_9 Int))
                                                      (=>
                                                         (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                                         (let
                                                            ((r.0$2_0 _$2_9))
                                                            (let
                                                               ((r.1$2_0 r.0$2_0))
                                                               (let
                                                                  ((result$2 r.1$2_0))
                                                                  (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       _$2_1
                                       (let
                                          ((_$2_2 (- m$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE _$1_4 1 _$2_2 1)
                                             (forall
                                                ((_$1_5 Int)
                                                 (_$2_3 Int))
                                                (=>
                                                   (INV_REC_f _$1_4 1 _$2_2 1 _$1_5 _$2_3)
                                                   (let
                                                      ((r.0$1_0 _$1_5))
                                                      (let
                                                         ((r.1$1_0 r.0$1_0))
                                                         (let
                                                            ((result$1 r.1$1_0)
                                                             (r.1$2_0 _$2_3))
                                                            (let
                                                               ((result$2 r.1$2_0))
                                                               (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_4 (= m$2_0_old 1)))
                                          (=>
                                             _$2_4
                                             (let
                                                ((_$2_5 (+ n$2_0_old 1)))
                                                (let
                                                   ((r.0$2_0 _$2_5))
                                                   (let
                                                      ((r.1$2_0 r.0$2_0))
                                                      (let
                                                         ((result$2 r.1$2_0))
                                                         (and
                                                            (INV_REC_f__1_PRE _$1_4 1)
                                                            (forall
                                                               ((_$1_5 Int))
                                                               (=>
                                                                  (INV_REC_f__1 _$1_4 1 _$1_5)
                                                                  (let
                                                                     ((r.0$1_0 _$1_5))
                                                                     (let
                                                                        ((r.1$1_0 r.0$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0))
                                                                           (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_4 (= m$2_0_old 1)))
                                          (=>
                                             (not _$2_4)
                                             (let
                                                ((_$2_6 (- n$2_0_old 1)))
                                                (and
                                                   (INV_REC_f_PRE _$1_4 1 m$2_0_old _$2_6)
                                                   (forall
                                                      ((_$1_5 Int)
                                                       (_$2_7 Int))
                                                      (=>
                                                         (INV_REC_f _$1_4 1 m$2_0_old _$2_6 _$1_5 _$2_7)
                                                         (let
                                                            ((r.0$1_0 _$1_5))
                                                            (let
                                                               ((r.1$1_0 r.0$1_0))
                                                               (let
                                                                  ((result$1 r.1$1_0)
                                                                   (_$2_8 (- m$2_0_old 1)))
                                                                  (and
                                                                     (INV_REC_f__2_PRE _$2_8 _$2_7)
                                                                     (forall
                                                                        ((_$2_9 Int))
                                                                        (=>
                                                                           (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                                                           (let
                                                                              ((r.0$2_0 _$2_9))
                                                                              (let
                                                                                 ((r.1$2_0 r.0$2_0))
                                                                                 (let
                                                                                    ((result$2 r.1$2_0))
                                                                                    (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       _$2_4
                                       (let
                                          ((_$2_5 (+ n$2_0_old 1)))
                                          (let
                                             ((r.0$2_0 _$2_5))
                                             (let
                                                ((r.1$2_0 r.0$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (and
                                                      (INV_REC_f__1_PRE _$1_4 1)
                                                      (forall
                                                         ((_$1_5 Int))
                                                         (=>
                                                            (INV_REC_f__1 _$1_4 1 _$1_5)
                                                            (let
                                                               ((r.0$1_0 _$1_5))
                                                               (let
                                                                  ((r.1$1_0 r.0$1_0))
                                                                  (let
                                                                     ((result$1 r.1$1_0))
                                                                     (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       (not _$2_4)
                                       (let
                                          ((_$2_6 (- n$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE _$1_4 1 m$2_0_old _$2_6)
                                             (forall
                                                ((_$1_5 Int)
                                                 (_$2_7 Int))
                                                (=>
                                                   (INV_REC_f _$1_4 1 m$2_0_old _$2_6 _$1_5 _$2_7)
                                                   (let
                                                      ((r.0$1_0 _$1_5))
                                                      (let
                                                         ((r.1$1_0 r.0$1_0))
                                                         (let
                                                            ((result$1 r.1$1_0)
                                                             (_$2_8 (- m$2_0_old 1)))
                                                            (and
                                                               (INV_REC_f__2_PRE _$2_8 _$2_7)
                                                               (forall
                                                                  ((_$2_9 Int))
                                                                  (=>
                                                                     (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                                                     (let
                                                                        ((r.0$2_0 _$2_9))
                                                                        (let
                                                                           ((r.1$2_0 r.0$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       _$2_1
                                       (let
                                          ((_$2_2 (- m$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE m$1_0_old _$1_6 _$2_2 1)
                                             (forall
                                                ((_$1_7 Int)
                                                 (_$2_3 Int))
                                                (=>
                                                   (INV_REC_f m$1_0_old _$1_6 _$2_2 1 _$1_7 _$2_3)
                                                   (let
                                                      ((_$1_8 (- m$1_0_old 1))
                                                       (r.1$2_0 _$2_3))
                                                      (let
                                                         ((result$2 r.1$2_0))
                                                         (and
                                                            (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                            (forall
                                                               ((_$1_9 Int))
                                                               (=>
                                                                  (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                  (let
                                                                     ((r.0$1_0 _$1_9))
                                                                     (let
                                                                        ((r.1$1_0 r.0$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0))
                                                                           (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_4 (= m$2_0_old 1)))
                                          (=>
                                             _$2_4
                                             (let
                                                ((_$2_5 (+ n$2_0_old 1)))
                                                (let
                                                   ((r.0$2_0 _$2_5))
                                                   (let
                                                      ((r.1$2_0 r.0$2_0))
                                                      (let
                                                         ((result$2 r.1$2_0))
                                                         (and
                                                            (INV_REC_f__1_PRE m$1_0_old _$1_6)
                                                            (forall
                                                               ((_$1_7 Int))
                                                               (=>
                                                                  (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                                                  (let
                                                                     ((_$1_8 (- m$1_0_old 1)))
                                                                     (and
                                                                        (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                                        (forall
                                                                           ((_$1_9 Int))
                                                                           (=>
                                                                              (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                              (let
                                                                                 ((r.0$1_0 _$1_9))
                                                                                 (let
                                                                                    ((r.1$1_0 r.0$1_0))
                                                                                    (let
                                                                                       ((result$1 r.1$1_0))
                                                                                       (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 _$2_0
                                 (let
                                    ((_$2_1 (= n$2_0_old 0)))
                                    (=>
                                       (not _$2_1)
                                       (let
                                          ((_$2_4 (= m$2_0_old 1)))
                                          (=>
                                             (not _$2_4)
                                             (let
                                                ((_$2_6 (- n$2_0_old 1)))
                                                (and
                                                   (INV_REC_f_PRE m$1_0_old _$1_6 m$2_0_old _$2_6)
                                                   (forall
                                                      ((_$1_7 Int)
                                                       (_$2_7 Int))
                                                      (=>
                                                         (INV_REC_f m$1_0_old _$1_6 m$2_0_old _$2_6 _$1_7 _$2_7)
                                                         (let
                                                            ((_$1_8 (- m$1_0_old 1))
                                                             (_$2_8 (- m$2_0_old 1)))
                                                            (and
                                                               (INV_REC_f_PRE _$1_8 _$1_7 _$2_8 _$2_7)
                                                               (forall
                                                                  ((_$1_9 Int)
                                                                   (_$2_9 Int))
                                                                  (=>
                                                                     (INV_REC_f _$1_8 _$1_7 _$2_8 _$2_7 _$1_9 _$2_9)
                                                                     (let
                                                                        ((r.0$1_0 _$1_9))
                                                                        (let
                                                                           ((r.1$1_0 r.0$1_0))
                                                                           (let
                                                                              ((result$1 r.1$1_0)
                                                                               (r.0$2_0 _$2_9))
                                                                              (let
                                                                                 ((r.1$2_0 r.0$2_0))
                                                                                 (let
                                                                                    ((result$2 r.1$2_0))
                                                                                    (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       _$2_4
                                       (let
                                          ((_$2_5 (+ n$2_0_old 1)))
                                          (let
                                             ((r.0$2_0 _$2_5))
                                             (let
                                                ((r.1$2_0 r.0$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (and
                                                      (INV_REC_f__1_PRE m$1_0_old _$1_6)
                                                      (forall
                                                         ((_$1_7 Int))
                                                         (=>
                                                            (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                                            (let
                                                               ((_$1_8 (- m$1_0_old 1)))
                                                               (and
                                                                  (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                                  (forall
                                                                     ((_$1_9 Int))
                                                                     (=>
                                                                        (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                        (let
                                                                           ((r.0$1_0 _$1_9))
                                                                           (let
                                                                              ((r.1$1_0 r.0$1_0))
                                                                              (let
                                                                                 ((result$1 r.1$1_0))
                                                                                 (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1))
                               (_$2_0 (> m$2_0_old 0)))
                              (=>
                                 (not _$2_0)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       (not _$2_4)
                                       (let
                                          ((_$2_6 (- n$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE m$1_0_old _$1_6 m$2_0_old _$2_6)
                                             (forall
                                                ((_$1_7 Int)
                                                 (_$2_7 Int))
                                                (=>
                                                   (INV_REC_f m$1_0_old _$1_6 m$2_0_old _$2_6 _$1_7 _$2_7)
                                                   (let
                                                      ((_$1_8 (- m$1_0_old 1))
                                                       (_$2_8 (- m$2_0_old 1)))
                                                      (and
                                                         (INV_REC_f_PRE _$1_8 _$1_7 _$2_8 _$2_7)
                                                         (forall
                                                            ((_$1_9 Int)
                                                             (_$2_9 Int))
                                                            (=>
                                                               (INV_REC_f _$1_8 _$1_7 _$2_8 _$2_7 _$1_9 _$2_9)
                                                               (let
                                                                  ((r.0$1_0 _$1_9))
                                                                  (let
                                                                     ((r.1$1_0 r.0$1_0))
                                                                     (let
                                                                        ((result$1 r.1$1_0)
                                                                         (r.0$2_0 _$2_9))
                                                                        (let
                                                                           ((r.1$2_0 r.0$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 _$2_1
                                 (let
                                    ((_$2_2 (- m$2_0_old 1)))
                                    (and
                                       (INV_REC_f_PRE m$1_0_old _$1_6 _$2_2 1)
                                       (forall
                                          ((_$1_7 Int)
                                           (_$2_3 Int))
                                          (=>
                                             (INV_REC_f m$1_0_old _$1_6 _$2_2 1 _$1_7 _$2_3)
                                             (let
                                                ((_$1_8 (- m$1_0_old 1))
                                                 (r.1$2_0 _$2_3))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (and
                                                      (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                      (forall
                                                         ((_$1_9 Int))
                                                         (=>
                                                            (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                            (let
                                                               ((r.0$1_0 _$1_9))
                                                               (let
                                                                  ((r.1$1_0 r.0$1_0))
                                                                  (let
                                                                     ((result$1 r.1$1_0))
                                                                     (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       _$2_4
                                       (let
                                          ((_$2_5 (+ n$2_0_old 1)))
                                          (let
                                             ((r.0$2_0 _$2_5))
                                             (let
                                                ((r.1$2_0 r.0$2_0))
                                                (let
                                                   ((result$2 r.1$2_0))
                                                   (and
                                                      (INV_REC_f__1_PRE m$1_0_old _$1_6)
                                                      (forall
                                                         ((_$1_7 Int))
                                                         (=>
                                                            (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                                            (let
                                                               ((_$1_8 (- m$1_0_old 1)))
                                                               (and
                                                                  (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                                  (forall
                                                                     ((_$1_9 Int))
                                                                     (=>
                                                                        (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                        (let
                                                                           ((r.0$1_0 _$1_9))
                                                                           (let
                                                                              ((r.1$1_0 r.0$1_0))
                                                                              (let
                                                                                 ((result$1 r.1$1_0))
                                                                                 (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           _$2_0
                           (let
                              ((_$2_1 (= n$2_0_old 0)))
                              (=>
                                 (not _$2_1)
                                 (let
                                    ((_$2_4 (= m$2_0_old 1)))
                                    (=>
                                       (not _$2_4)
                                       (let
                                          ((_$2_6 (- n$2_0_old 1)))
                                          (and
                                             (INV_REC_f_PRE m$1_0_old _$1_6 m$2_0_old _$2_6)
                                             (forall
                                                ((_$1_7 Int)
                                                 (_$2_7 Int))
                                                (=>
                                                   (INV_REC_f m$1_0_old _$1_6 m$2_0_old _$2_6 _$1_7 _$2_7)
                                                   (let
                                                      ((_$1_8 (- m$1_0_old 1))
                                                       (_$2_8 (- m$2_0_old 1)))
                                                      (and
                                                         (INV_REC_f_PRE _$1_8 _$1_7 _$2_8 _$2_7)
                                                         (forall
                                                            ((_$1_9 Int)
                                                             (_$2_9 Int))
                                                            (=>
                                                               (INV_REC_f _$1_8 _$1_7 _$2_8 _$2_7 _$1_9 _$2_9)
                                                               (let
                                                                  ((r.0$1_0 _$1_9))
                                                                  (let
                                                                     ((r.1$1_0 r.0$1_0))
                                                                     (let
                                                                        ((result$1 r.1$1_0)
                                                                         (r.0$2_0 _$2_9))
                                                                        (let
                                                                           ((r.1$2_0 r.0$2_0))
                                                                           (let
                                                                              ((result$2 r.1$2_0))
                                                                              (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (= m$2_0_old 1)))
                              (=>
                                 _$2_4
                                 (let
                                    ((_$2_5 (+ n$2_0_old 1)))
                                    (let
                                       ((r.0$2_0 _$2_5))
                                       (let
                                          ((r.1$2_0 r.0$2_0))
                                          (let
                                             ((result$2 r.1$2_0))
                                             (and
                                                (INV_REC_f__1_PRE m$1_0_old _$1_6)
                                                (forall
                                                   ((_$1_7 Int))
                                                   (=>
                                                      (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                                      (let
                                                         ((_$1_8 (- m$1_0_old 1)))
                                                         (and
                                                            (INV_REC_f__1_PRE _$1_8 _$1_7)
                                                            (forall
                                                               ((_$1_9 Int))
                                                               (=>
                                                                  (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                                  (let
                                                                     ((r.0$1_0 _$1_9))
                                                                     (let
                                                                        ((r.1$1_0 r.0$1_0))
                                                                        (let
                                                                           ((result$1 r.1$1_0))
                                                                           (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2))))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int)
       (m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f_PRE m$1_0_old n$1_0_old m$2_0_old n$2_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1))
                         (_$2_0 (> m$2_0_old 0)))
                        (=>
                           (not _$2_0)
                           (let
                              ((_$2_4 (= m$2_0_old 1)))
                              (=>
                                 (not _$2_4)
                                 (let
                                    ((_$2_6 (- n$2_0_old 1)))
                                    (and
                                       (INV_REC_f_PRE m$1_0_old _$1_6 m$2_0_old _$2_6)
                                       (forall
                                          ((_$1_7 Int)
                                           (_$2_7 Int))
                                          (=>
                                             (INV_REC_f m$1_0_old _$1_6 m$2_0_old _$2_6 _$1_7 _$2_7)
                                             (let
                                                ((_$1_8 (- m$1_0_old 1))
                                                 (_$2_8 (- m$2_0_old 1)))
                                                (and
                                                   (INV_REC_f_PRE _$1_8 _$1_7 _$2_8 _$2_7)
                                                   (forall
                                                      ((_$1_9 Int)
                                                       (_$2_9 Int))
                                                      (=>
                                                         (INV_REC_f _$1_8 _$1_7 _$2_8 _$2_7 _$1_9 _$2_9)
                                                         (let
                                                            ((r.0$1_0 _$1_9))
                                                            (let
                                                               ((r.1$1_0 r.0$1_0))
                                                               (let
                                                                  ((result$1 r.1$1_0)
                                                                   (r.0$2_0 _$2_9))
                                                                  (let
                                                                     ((r.1$2_0 r.0$2_0))
                                                                     (let
                                                                        ((result$2 r.1$2_0))
                                                                        (INV_REC_f m$1_0_old n$1_0_old m$2_0_old n$2_0_old result$1 result$2)))))))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE m$1_0_old n$1_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               _$1_0
               (let
                  ((_$1_1 (+ n$1_0_old 1)))
                  (let
                     ((r.1$1_0 _$1_1))
                     (let
                        ((result$1 r.1$1_0))
                        (INV_REC_f__1 m$1_0_old n$1_0_old result$1)))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE m$1_0_old n$1_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           _$1_3
                           (let
                              ((_$1_4 (- m$1_0_old 1)))
                              (and
                                 (INV_REC_f__1_PRE _$1_4 1)
                                 (forall
                                    ((_$1_5 Int))
                                    (=>
                                       (INV_REC_f__1 _$1_4 1 _$1_5)
                                       (let
                                          ((r.0$1_0 _$1_5))
                                          (let
                                             ((r.1$1_0 r.0$1_0))
                                             (let
                                                ((result$1 r.1$1_0))
                                                (INV_REC_f__1 m$1_0_old n$1_0_old result$1)))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE m$1_0_old n$1_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     _$1_2
                     (let
                        ((_$1_3 (= n$1_0_old 0)))
                        (=>
                           (not _$1_3)
                           (let
                              ((_$1_6 (- n$1_0_old 1)))
                              (and
                                 (INV_REC_f__1_PRE m$1_0_old _$1_6)
                                 (forall
                                    ((_$1_7 Int))
                                    (=>
                                       (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                       (let
                                          ((_$1_8 (- m$1_0_old 1)))
                                          (and
                                             (INV_REC_f__1_PRE _$1_8 _$1_7)
                                             (forall
                                                ((_$1_9 Int))
                                                (=>
                                                   (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                                   (let
                                                      ((r.0$1_0 _$1_9))
                                                      (let
                                                         ((r.1$1_0 r.0$1_0))
                                                         (let
                                                            ((result$1 r.1$1_0))
                                                            (INV_REC_f__1 m$1_0_old n$1_0_old result$1)))))))))))))))))))))
(assert
   (forall
      ((m$1_0_old Int)
       (n$1_0_old Int))
      (=>
         (INV_REC_f__1_PRE m$1_0_old n$1_0_old)
         (let
            ((_$1_0 (= m$1_0_old 0)))
            (=>
               (not _$1_0)
               (let
                  ((_$1_2 (> m$1_0_old 0)))
                  (=>
                     (not _$1_2)
                     (let
                        ((_$1_6 (- n$1_0_old 1)))
                        (and
                           (INV_REC_f__1_PRE m$1_0_old _$1_6)
                           (forall
                              ((_$1_7 Int))
                              (=>
                                 (INV_REC_f__1 m$1_0_old _$1_6 _$1_7)
                                 (let
                                    ((_$1_8 (- m$1_0_old 1)))
                                    (and
                                       (INV_REC_f__1_PRE _$1_8 _$1_7)
                                       (forall
                                          ((_$1_9 Int))
                                          (=>
                                             (INV_REC_f__1 _$1_8 _$1_7 _$1_9)
                                             (let
                                                ((r.0$1_0 _$1_9))
                                                (let
                                                   ((r.1$1_0 r.0$1_0))
                                                   (let
                                                      ((result$1 r.1$1_0))
                                                      (INV_REC_f__1 m$1_0_old n$1_0_old result$1)))))))))))))))))))
(assert
   (forall
      ((m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old n$2_0_old)
         (let
            ((_$2_0 (> m$2_0_old 0)))
            (=>
               _$2_0
               (let
                  ((_$2_1 (= n$2_0_old 0)))
                  (=>
                     _$2_1
                     (let
                        ((_$2_2 (- m$2_0_old 1)))
                        (and
                           (INV_REC_f__2_PRE _$2_2 1)
                           (forall
                              ((_$2_3 Int))
                              (=>
                                 (INV_REC_f__2 _$2_2 1 _$2_3)
                                 (let
                                    ((r.1$2_0 _$2_3))
                                    (let
                                       ((result$2 r.1$2_0))
                                       (INV_REC_f__2 m$2_0_old n$2_0_old result$2))))))))))))))
(assert
   (forall
      ((m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old n$2_0_old)
         (let
            ((_$2_0 (> m$2_0_old 0)))
            (=>
               _$2_0
               (let
                  ((_$2_1 (= n$2_0_old 0)))
                  (=>
                     (not _$2_1)
                     (let
                        ((_$2_4 (= m$2_0_old 1)))
                        (=>
                           _$2_4
                           (let
                              ((_$2_5 (+ n$2_0_old 1)))
                              (let
                                 ((r.0$2_0 _$2_5))
                                 (let
                                    ((r.1$2_0 r.0$2_0))
                                    (let
                                       ((result$2 r.1$2_0))
                                       (INV_REC_f__2 m$2_0_old n$2_0_old result$2))))))))))))))
(assert
   (forall
      ((m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old n$2_0_old)
         (let
            ((_$2_0 (> m$2_0_old 0)))
            (=>
               _$2_0
               (let
                  ((_$2_1 (= n$2_0_old 0)))
                  (=>
                     (not _$2_1)
                     (let
                        ((_$2_4 (= m$2_0_old 1)))
                        (=>
                           (not _$2_4)
                           (let
                              ((_$2_6 (- n$2_0_old 1)))
                              (and
                                 (INV_REC_f__2_PRE m$2_0_old _$2_6)
                                 (forall
                                    ((_$2_7 Int))
                                    (=>
                                       (INV_REC_f__2 m$2_0_old _$2_6 _$2_7)
                                       (let
                                          ((_$2_8 (- m$2_0_old 1)))
                                          (and
                                             (INV_REC_f__2_PRE _$2_8 _$2_7)
                                             (forall
                                                ((_$2_9 Int))
                                                (=>
                                                   (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                                   (let
                                                      ((r.0$2_0 _$2_9))
                                                      (let
                                                         ((r.1$2_0 r.0$2_0))
                                                         (let
                                                            ((result$2 r.1$2_0))
                                                            (INV_REC_f__2 m$2_0_old n$2_0_old result$2)))))))))))))))))))))
(assert
   (forall
      ((m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old n$2_0_old)
         (let
            ((_$2_0 (> m$2_0_old 0)))
            (=>
               (not _$2_0)
               (let
                  ((_$2_4 (= m$2_0_old 1)))
                  (=>
                     _$2_4
                     (let
                        ((_$2_5 (+ n$2_0_old 1)))
                        (let
                           ((r.0$2_0 _$2_5))
                           (let
                              ((r.1$2_0 r.0$2_0))
                              (let
                                 ((result$2 r.1$2_0))
                                 (INV_REC_f__2 m$2_0_old n$2_0_old result$2))))))))))))
(assert
   (forall
      ((m$2_0_old Int)
       (n$2_0_old Int))
      (=>
         (INV_REC_f__2_PRE m$2_0_old n$2_0_old)
         (let
            ((_$2_0 (> m$2_0_old 0)))
            (=>
               (not _$2_0)
               (let
                  ((_$2_4 (= m$2_0_old 1)))
                  (=>
                     (not _$2_4)
                     (let
                        ((_$2_6 (- n$2_0_old 1)))
                        (and
                           (INV_REC_f__2_PRE m$2_0_old _$2_6)
                           (forall
                              ((_$2_7 Int))
                              (=>
                                 (INV_REC_f__2 m$2_0_old _$2_6 _$2_7)
                                 (let
                                    ((_$2_8 (- m$2_0_old 1)))
                                    (and
                                       (INV_REC_f__2_PRE _$2_8 _$2_7)
                                       (forall
                                          ((_$2_9 Int))
                                          (=>
                                             (INV_REC_f__2 _$2_8 _$2_7 _$2_9)
                                             (let
                                                ((r.0$2_0 _$2_9))
                                                (let
                                                   ((r.1$2_0 r.0$2_0))
                                                   (let
                                                      ((result$2 r.1$2_0))
                                                      (INV_REC_f__2 m$2_0_old n$2_0_old result$2)))))))))))))))))))
; FORBIDDEN PATHS
; OFF BY N
(check-sat)
(get-model)
