; A literal's intrinsic type is distinct from an authored arrow annotation.
(: true (-> $z Number))
(: cc-inner (-> (-> $a Number) Number Number))
(= (cc-inner $f $n) (if (== $n 0) 0 (cc-inner true (- $n 1))))
(: cc-outer (-> Number Number))
(= (cc-outer $n) (cc-inner true $n))
!(get-type true)
!(collapse (cc-outer 2))
!(collapse (cc-inner true 2))
