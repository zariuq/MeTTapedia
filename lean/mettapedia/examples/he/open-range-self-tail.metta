; A self-tail call replaces the structural argument with a different instance.
; The base branch returns its parameter; both declarations use the same
; source range, but the two activations do not owe the same instantiated range.
(: List (-> Type Type))
(: NList (List Number))
(: SList (List String))
(: range-flip (-> Bool (List $a) (List $a)))
(= (range-flip $flag $xs)
   (if $flag $xs (range-flip True SList)))
!(range-flip True NList)
!(range-flip False NList)
