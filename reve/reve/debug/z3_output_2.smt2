(derivation
 (step s!4
       (INV_MAIN!3 0 0 2 2 (- 1798)
                   (store (store ((as const (Array Int Int)) 3) (- 1797) 17) (- 1) 16)
                   0 (- 1798) 2 2 (- 1798) 0
                   (store (store ((as const (Array Int Int)) 3) (- 1797) 17) (- 1) 16)
                   4 (- 2))
       rule!1  (subst
                (= dest$1 0)
                (= nbytes$1 2)
                (= src$1 (- 1798))
                (= HEAP$1 (store (store ((as const (Array Int Int)) 3) (- 1797) 17) (- 1) 16))
                (= len$2 2)
                (= src$2 (- 1798))
                (= to$2 0)
                (= HEAP$2 (store (store ((as const (Array Int Int)) 3) (- 1797) 17) (- 1) 16))
                )
       (labels  )
       (ref   ))
 (step s!3 (INV_MAIN!3 0 2 2 2 (- 1798)
                       (store (store (store ((as const (Array Int Int)) 3) (- 1797) 17)(- 1) 16) 0 16)
                       2 (- 1798) 2 0 (- 1796) 0
                       (store (store (store ((as const (Array Int Int)) 3) (- 1797) 17) (- 1) 16) 0 17)
                       4 (- 2))
       rule!3  (subst
                (= mul$1 2)
                (= nbytes$1 2)
                (= dest$1 0)
                (= HEAP$1 (store (store ((as const (Array Int Int)) 3) (- 1797) 17) (- 1) 16))
                (= src$1 (- 1798))
                (= i.0$1 0)
                (= src$2 (- 1798))
                (= len$2 2)
                (= len.addr.0$2 0)
                (= to$2 0)
                (= dst.0$2 0)
                (= HEAP$2 (store (store ((as const (Array Int Int)) 3) (- 1797) 17) (- 1) 16))
                (= src.0$2 0)
                )
       (labels  )
       (ref  s!4  ))
 (step s!2 (END_QUERY)
       rule!2  (subst
                (= dest$1 0)
                (= nbytes$1 2)
                (= src$1 (- 1798))
                (= dst.0$2 2)
                (= src$2 (- 1798))
                (= len$2 2)
                (= src.0$2 (- 1796))
                (= to$2 0)
                (= i.0$1 2)
                (= mul$1 2)
                (= len.addr.0$2 0)
                (= HEAP$1 (store (store (store ((as const (Array Int Int)) 3) (- 1797) 17) (- 1) 16) 0 16))
                (= HEAP$2 (store (store (store ((as const (Array Int Int)) 3) (- 1797) 17) (- 1) 16) 0 17))
                )
       (labels  )
       (ref  s!3  ))
 (step s!1 (@Fail!0)
       rule!4  (subst
                )
       (labels  )
       (ref  s!2  ))
 )
(model
 "@a_9!1_3 -> 4
to$2_3 -> 2
@b_4 -> true
@a_2_4 -> 2
@b_1 -> true
@a_1_3 -> 2
@under4 -> false
@a_9_4 -> 2
@a_10_4 -> (- 1798)
@p_@a_10!2_2 -> (- 2)
@a_11_4 -> 0
@under2 -> false
@a_9!1_4 -> 4
@a_10!2_4 -> (- 2)
@p_@a_9!1_2 -> 4
@a_1_4 -> 0
@b_2 -> true
HEAP$2_3 -> (_ as-array k!60)
@a_10_3 -> (- 1796)
HEAP$1_3 -> (_ as-array k!59)
@a_9_3 -> 0
@b_3 -> true
@a_10!2_3 -> (- 2)
@under3 -> false
k!59 -> {
  0 -> 16
  (- 1) -> 16
  (- 1797) -> 17
  else -> 3
}
k!60 -> {
  0 -> 17
  (- 1) -> 16
  (- 1797) -> 17
  else -> 3
}
k!61 -> {
  (- 1) -> 16
  (- 1797) -> 17
  else -> 3
}
")
