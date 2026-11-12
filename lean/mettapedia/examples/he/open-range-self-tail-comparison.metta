; A self-tail replacement under a comparison-shaped condition.
(: List (-> Type Type))
(: NList (List Number))
(: SList (List String))
(: range-step (-> Number (List $a) (List $a)))
(= (range-step $n $xs)
   (if (== $n 0) $xs (range-step 0 SList)))
!(range-step 0 NList)
!(range-step 1 NList)
