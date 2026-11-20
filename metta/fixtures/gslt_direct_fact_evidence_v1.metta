(gslt-presentation-v1 StructuralFactEvidenceV1
  (signature
    (operator HoldsV1 1)
    (operator HoldsNullaryV1 0)
    (operator cons 2)
    (operator quote 1)
    (operator let 3)
    (operator nil 0)
    (operator λ 1))
  (equations)
  (rewrites
    (rule constructor-names
      (head (HoldsV1 (cons ?x (quote (nil)))))
      (body))
    (rule slot-collision
      (head (HoldsV1 (let ?__gslt_input_v1_0_0 ?x ?x)))
      (body))
    (rule nullary-data
      (head (HoldsV1 (nil)))
      (body))
    (rule unicode-data
      (head (HoldsV1 (λ ?x)))
      (body))
    (rule duplicate-occurrence
      (head (HoldsV1 (cons ?x (quote (nil)))))
      (body))
    (rule integer-value
      (head (HoldsV1 9007199254740993))
      (body))
    (rule boolean-value
      (head (HoldsV1 True))
      (body))
    (rule string-value
      (head (HoldsV1 "True"))
      (body))
    (rule string-variable-spelling
      (head (HoldsV1 "$__gslt_input_v1_0_0 λ\n\u0000"))
      (body))
    (rule nullary-relation
      (head (HoldsNullaryV1))
      (body))))
