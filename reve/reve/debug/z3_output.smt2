(derivation
 (step s!4 (INV_MAIN!3 1323 0 2 3 346
                       (store (store (store (store ((as const (Array Int Int)) 4)
                                                   347 22)
                                            7228 8)
                                     7229 21)
                              346 7)
                       1323 346 3 3 346 1323
                       (store (store (store (store ((as const (Array Int Int)) 4)
                                                   347 22)
                                            7228 8)
                                     7229 21)
                              346 7)
                       5 7228)
       rule!1  (subst
                (= dest$1 1323)
                (= nbytes$1 3)
                (= src$1 346)
                (= HEAP$1 (store (store (store (store ((as const (Array Int Int)) 4)
                                                      347 22)
                                               7228 8)
                                        7229 21)
                                 346 7))
                (= len$2 3)
                (= src$2 346)
                (= to$2 1323)
                (= HEAP$2 (store (store (store (store ((as const (Array Int Int)) 4)
                                                      347 22)
                                               7228 8)
                                        7229 21)
                                 346 7))
                )
       (labels  )
       (ref   ))
 (step s!3 (INV_MAIN!3 1323 2 2 3 346
                       (store (store (store (store (store (store ((as const (Array Int Int)) 4)
                                                                 1324 8)
                                                          347 22)
                                                   7228 8)
                                            346 7)
                                     7229 21)
                              1323 21)
                       1325 346 3 1 348 1323
                       (store (store (store (store (store (store ((as const (Array Int Int)) 4)
                                                                 1324 7)
                                                          347 22)
                                                   7228 8)
                                            346 7)
                                     7229 21)
                              1323 22)
                       5 7228)
       rule!3  (subst
                (= mul$1 2)
                (= nbytes$1 3)
                (= dest$1 1323)
                (= HEAP$1 (store (store (store (store ((as const (Array Int Int)) 4)
                                                      347 22)
                                               7228 8)
                                        7229 21)
                                 346 7))
                (= src$1 346)
                (= i.0$1 0)
                (= src$2 346)
                (= len$2 3)
                (= len.addr.0$2 0)
                (= to$2 1323)
                (= dst.0$2 0)
                (= HEAP$2 (store (store (store (store ((as const (Array Int Int)) 4)
                                                      347 22)
                                               7228 8)
                                        7229 21)
                                 346 7))
                (= src.0$2 0)
                )
       (labels  )
       (ref  s!4  ))
 (step s!2 (END_QUERY)
       rule!2  (subst
                (= dest$1 1323)
                (= nbytes$1 3)
                (= src$1 346)
                (= dst.0$2 1325)
                (= src$2 346)
                (= len$2 3)
                (= src.0$2 348)
                (= to$2 1323)
                (= i.0$1 2)
                (= mul$1 2)
                (= len.addr.0$2 1)
                (= HEAP$1 (store (store (store (store (store (store ((as const (Array Int Int)) 4)
                                                                    1324 8)
                                                             347 22)
                                                      7228 8)
                                               346 7)
                                        7229 21)
                                 1323 21))
                (= HEAP$2 (store (store (store (store (store (store ((as const (Array Int Int)) 4)
                                                                    1324 7)
                                                             347 22)
                                                      7228 8)
                                               346 7)
                                        7229 21)
                                 1323 22))
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
to$2_3 -> 1325
@b_4 -> true
@a_2_4 -> 2
@b_1 -> true
@a_1_3 -> 2
@under4 -> false
@a_9_4 -> 3
@a_10_4 -> 346
@p_@a_10!2_2 -> 7228
@a_11_4 -> 1323
@under2 -> false
@a_9!1_4 -> 5
@a_10!2_4 -> 7228
@p_@a_9!1_2 -> 5
@a_1_4 -> 0
@b_2 -> true
HEAP$2_3 -> (_ as-array k!65)
@a_10_3 -> 348
HEAP$1_3 -> (_ as-array k!64)
@a_9_3 -> 1
@b_3 -> true
@a_10!2_3 -> 7228
@under3 -> false
k!67 -> {
  1323 -> 22
  7229 -> 21
  346 -> 7
  7228 -> 8
  347 -> 22
  else -> 4
}
k!64 -> {
  1323 -> 21
  7229 -> 21
  346 -> 7
  7228 -> 8
  347 -> 22
  1324 -> 8
  else -> 4
}
k!68 -> {
  346 -> 7
  7229 -> 21
  7228 -> 8
  347 -> 22
  else -> 4
}
k!65 -> {
  1323 -> 22
  7229 -> 21
  346 -> 7
  7228 -> 8
  347 -> 22
  1324 -> 7
  else -> 4
}
k!66 -> {
  1323 -> 21
  7229 -> 21
  346 -> 7
  7228 -> 8
  347 -> 22
  else -> 4
}
")
