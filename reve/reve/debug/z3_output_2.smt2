(derivation
 (step s!4
       (INV_MAIN!3
        449 0 2 2 446
        (store (store ((as const (Array Int Int)) 4)
                      446 15) 447 16)
        449 446 2 2 446 449
        (store (store ((as const (Array Int Int)) 4)
                      446 15) 447 16)
        5 445)
 rule!1  (subst
    (= dest$1 449)
    (= nbytes$1 2)
    (= src$1 446)
    (= HEAP$1 (store (store ((as const (Array Int Int)) 4)
                            446 15) 447 16))
    (= len$2 2)
    (= src$2 446)
    (= to$2 449)
    (= HEAP$2 (store (store ((as const (Array Int Int)) 4)
                            446 15) 447 16))
  )
  (labels  )
  (ref   ))
 (step s!3
       (INV_MAIN!3
        449 2 2 2 446
        (store (store (store ((as const (Array Int Int)) 4) 446 15)
                      447 16) 449 15)
        451 446 2 0 448 449
        (store (store (store ((as const (Array Int Int)) 4) 446 15)
                      447 16) 449 16)
        5 445)
 rule!3  (subst
    (= i.0$1 0)
    (= mul$1 2)
    (= nbytes$1 2)
    (= dest$1 449)
    (= HEAP$1 (store (store ((as const (Array Int Int)) 4) 446 15) 447 16))
    (= src$1 446)
    (= src$2 446)
    (= len$2 2)
    (= len.addr.0$2 0)
    (= to$2 449)
    (= dst.0$2 0)
    (= HEAP$2 (store (store ((as const (Array Int Int)) 4) 446 15) 447 16))
    (= src.0$2 0)
  )
  (labels  )
  (ref  s!4  ))
(step s!2 (END_QUERY)
 rule!2  (subst
    (= dest$1 449)
    (= nbytes$1 2)
    (= src$1 446)
    (= dst.0$2 451)
    (= src$2 446)
    (= len$2 2)
    (= src.0$2 448)
    (= to$2 449)
    (= i.0$1 2)
    (= mul$1 2)
    (= len.addr.0$2 0)
    (= HEAP$1 (store (store (store ((as const (Array Int Int)) 4) 446 15) 447 16) 449 15))
    (= HEAP$2 (store (store (store ((as const (Array Int Int)) 4) 446 15) 447 16) 449 16))
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
"@a_9!1_3 -> 5
to$2_3 -> 451
@b_4 -> true
@a_2_4 -> 2
@b_1 -> true
@a_1_3 -> 2
@under4 -> false
@a_9_4 -> 2
@a_10_4 -> 446
@p_@a_10!2_2 -> 445
@a_11_4 -> 449
@under2 -> false
@a_9!1_4 -> 5
@a_10!2_4 -> 445
@p_@a_9!1_2 -> 5
@a_1_4 -> 0
@b_2 -> true
HEAP$2_3 -> (_ as-array k!60)
@a_10_3 -> 448
HEAP$1_3 -> (_ as-array k!59)
@a_9_3 -> 0
@b_3 -> true
@a_10!2_3 -> 445
@under3 -> false
k!59 -> {
  449 -> 15
  447 -> 16
  446 -> 15
  else -> 4
}
k!60 -> {
  449 -> 16
  447 -> 16
  446 -> 15
  else -> 4
}
k!61 -> {
  447 -> 16
  446 -> 15
  else -> 4
}
")
