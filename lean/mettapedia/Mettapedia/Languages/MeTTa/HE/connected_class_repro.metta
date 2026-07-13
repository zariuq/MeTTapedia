; Connected equality-class conformance repro.
;
; Hyperon evaluates all three assertions to ().  Current LeaTTa passes the
; first alpha-collapse check, then fails the binding-readout and atom-level
; checks because addVarBinding discards the successful rebind unifier.

; Two edges: equation answers differ only by a variable name, so they remain
; alpha-equivalent.
(= (g2 $p $p) (h $p))
!(assertAlphaEqual (g2 $q1 $q2) (h $x))

; The same two-edge case is already visible when both query variables are read
; back from the unifier.
!(assertAlphaEqual
    (unify ($p $p) ($q1 $q2) ($q1 $q2) no-match)
    ($x $x))

; Three edges: the ordinary equation result itself becomes alpha-distinct.
(= (g $p1 $p2 $p2) (f $p1 $p2))
!(assertAlphaEqual (g $q1 $q1 $q2) (f $x $x))
