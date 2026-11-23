; Written match keeps its pattern and template as source syntax.
; These deliberately incompatible declarations must not select an
; ordinary grounded-function argument protocol for the written form.
(row 7)
(: match (-> Number Number Number Number))
!(collapse (match &self (row $x) $x))
!(collapse (match &self (row $x) (+ $x 1)))
(= (keep-written-match $x) (match &self (row $r) $x))
!(collapse (keep-written-match 4))
