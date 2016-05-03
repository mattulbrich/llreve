(set-logic HORN)
(define-fun
   IN_INV
   ((n$1_0 Int)
    (n$2_0 Int))
   Bool
   (and
      (= n$1_0 n$2_0)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int))
   Bool
   (= result$1 result$2))
(define-fun INV_MAIN_42 ((.n$1_0 Int) (i.0$1_0 Int) (j.0$1_0 Int) (.n$2_0 Int) (i.0$2_0 Int) (j.0$2_0 Int) (mark42$1 Int) (mark42$2 Int)) Bool
  (or (and (= (- i.0$2_0 i.0$1_0) (- 1))
           (= .n$1_0 .n$2_0)
           (= j.0$1_0 j.0$2_0)
           (> mark42$1 mark42$2)
           (= mark42$1 (- i.0$1_0 1))
           (= mark42$2 (- i.0$2_0 1))
           (= mark42$1 .n$1_0)
           (= mark42$2 (- .n$2_0 1))
           )
      (and (= .n$1_0 .n$2_0)
           (= i.0$2_0 i.0$1_0)
           (= (- j.0$1_0 j.0$2_0) (- 2))
           (= mark42$1 mark42$2)
           (= mark42$1 (- i.0$1_0 1))
           (= mark42$2 (- i.0$2_0 1))
           (>= .n$1_0 i.0$1_0)
           )))
(assert
   (forall
      ((n$1_0_old Int)
       (n$2_0_old Int))
      (=>
         (IN_INV n$1_0_old n$2_0_old)
         (let
            ((n$1_0 n$1_0_old)
             (n$2_0 n$2_0_old))
           (let
               ((_$1_0 (< n$1_0 1)))
               (let
                  ((.n$1_0 (ite _$1_0 1 n$1_0))
                   (j.0$1_0 0)
                   (i.0$1_0 1)
                   (n$2_0 n$2_0_old))
                  (let
                     ((_$2_0 (< n$2_0 1)))
                     (let
                        ((.n$2_0 (ite _$2_0 1 n$2_0))
                         (j.0$2_0 2)
                         (i.0$2_0 1))
                        (INV_MAIN_42 .n$1_0 i.0$1_0 j.0$1_0 .n$2_0 i.0$2_0 j.0$2_0 0 0)))))))))
(assert
   (forall
      ((.n$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (.n$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (mark42$1 Int)
       (mark42$2 Int))
      (=>
       (and
        (INV_MAIN_42 .n$1_0_old i.0$1_0_old j.0$1_0_old .n$2_0_old i.0$2_0_old j.0$2_0_old mark42$1 mark42$2)
        (>= mark42$1 0)
        (>= mark42$2 0))
         (let
            ((.n$1_0 .n$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((j.0$1_0 j.0$1_0_old)
                (_$1_3 (<= i.0$1_0 .n$1_0)))
               (=>
                  (not _$1_3)
                  (let
                     ((result$1 j.0$1_0)
                      (.n$2_0 .n$2_0_old)
                      (i.0$2_0 i.0$2_0_old))
                     (let
                        ((j.0$2_0 j.0$2_0_old)
                         (_$2_3 (< i.0$2_0 .n$2_0)))
                        (=>
                           (not _$2_3)
                           (let
                              ((result$2 j.0$2_0))
                              (OUT_INV result$1 result$2)))))))))))
(assert
   (forall
      ((.n$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (.n$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (mark42$1 Int)
       (mark42$2 Int))
      (=>
       (and (INV_MAIN_42 .n$1_0_old i.0$1_0_old j.0$1_0_old .n$2_0_old i.0$2_0_old j.0$2_0_old mark42$1 mark42$2)
            (= mark42$1 mark42$2)
            (>= mark42$1 0)
            (>= mark42$2 0))
         (let
            ((.n$1_0 .n$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((j.0$1_0 j.0$1_0_old)
                (_$1_3 (<= i.0$1_0 .n$1_0)))
               (=>
                  _$1_3
                  (let
                     ((_$1_4 (+ j.0$1_0 2))
                      (_$1_5 (+ i.0$1_0 1)))
                     (let
                        ((j.0$1_0 _$1_4)
                         (i.0$1_0 _$1_5)
                         (.n$2_0 .n$2_0_old)
                         (i.0$2_0 i.0$2_0_old))
                        (let
                           ((j.0$2_0 j.0$2_0_old)
                            (_$2_3 (< i.0$2_0 .n$2_0)))
                           (=>
                              _$2_3
                              (let
                                 ((_$2_4 (+ j.0$2_0 2))
                                  (_$2_5 (+ i.0$2_0 1)))
                                 (let
                                    ((j.0$2_0 _$2_4)
                                     (i.0$2_0 _$2_5))
                                    (INV_MAIN_42 .n$1_0 i.0$1_0 j.0$1_0 .n$2_0 i.0$2_0 j.0$2_0 (+ mark42$1 1) (+ mark42$2 1))))))))))))))
(assert
   (forall
      ((.n$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (.n$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (mark42$1 Int)
       (mark42$2 Int))
      (=>
       (and
        (INV_MAIN_42 .n$1_0_old i.0$1_0_old j.0$1_0_old .n$2_0_old i.0$2_0_old j.0$2_0_old mark42$1 mark42$2)
        (> (+ mark42$1 1) mark42$2)
        (>= mark42$1 0)
        (>= mark42$2 0))
         (let
            ((.n$1_0 .n$1_0_old)
             (i.0$1_0 i.0$1_0_old))
            (let
               ((j.0$1_0 j.0$1_0_old)
                (_$1_3 (<= i.0$1_0 .n$1_0)))
               (=>
                  _$1_3
                  (let
                     ((_$1_4 (+ j.0$1_0 2))
                      (_$1_5 (+ i.0$1_0 1)))
                     (let
                        ((j.0$1_0 _$1_4)
                         (i.0$1_0 _$1_5))
                        (=>
                           (and
                              (let
                                 ((.n$2_0 .n$2_0_old)
                                  (i.0$2_0 i.0$2_0_old))
                                 (let
                                    ((j.0$2_0 j.0$2_0_old)
                                     (_$2_3 (< i.0$2_0 .n$2_0)))
                                    (=>
                                       _$2_3
                                       (let
                                          ((_$2_4 (+ j.0$2_0 2))
                                           (_$2_5 (+ i.0$2_0 1)))
                                          (let
                                             ((j.0$2_0 _$2_4)
                                              (i.0$2_0 _$2_5))
                                             false))))))
                           (INV_MAIN_42 .n$1_0 i.0$1_0 j.0$1_0 .n$2_0_old i.0$2_0_old j.0$2_0_old (+ mark42$1 1) mark42$2))))))))))
(assert
   (forall
      ((.n$1_0_old Int)
       (i.0$1_0_old Int)
       (j.0$1_0_old Int)
       (.n$2_0_old Int)
       (i.0$2_0_old Int)
       (j.0$2_0_old Int)
       (mark42$1 Int)
       (mark42$2 Int))
      (=>
       (and
        (INV_MAIN_42 .n$1_0_old i.0$1_0_old j.0$1_0_old .n$2_0_old i.0$2_0_old j.0$2_0_old mark42$1 mark42$2)
        (> (+ mark42$2 1) mark42$1)
        (>= mark42$1 0)
        (>= mark42$2 0))
         (let
            ((.n$2_0 .n$2_0_old)
             (i.0$2_0 i.0$2_0_old))
            (let
               ((j.0$2_0 j.0$2_0_old)
                (_$2_3 (< i.0$2_0 .n$2_0)))
               (=>
                  _$2_3
                  (let
                     ((_$2_4 (+ j.0$2_0 2))
                      (_$2_5 (+ i.0$2_0 1)))
                     (let
                        ((j.0$2_0 _$2_4)
                         (i.0$2_0 _$2_5))
                        (=>
                           (and
                              (let
                                 ((.n$1_0 .n$1_0_old)
                                  (i.0$1_0 i.0$1_0_old))
                                 (let
                                    ((j.0$1_0 j.0$1_0_old)
                                     (_$1_3 (<= i.0$1_0 .n$1_0)))
                                    (=>
                                       _$1_3
                                       (let
                                          ((_$1_4 (+ j.0$1_0 2))
                                           (_$1_5 (+ i.0$1_0 1)))
                                          (let
                                             ((j.0$1_0 _$1_4)
                                              (i.0$1_0 _$1_5))
                                             false))))))
                           (INV_MAIN_42 .n$1_0_old i.0$1_0_old j.0$1_0_old .n$2_0 i.0$2_0 j.0$2_0 mark42$1 (+ mark42$2 1)))))))))))
(check-sat)
(get-model)
