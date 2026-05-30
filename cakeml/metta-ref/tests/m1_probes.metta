; M1 pure symbolic HE-style MeTTa capacity probes.
; These are semantic witnesses; the first implementation currently builds the
; same ASTs directly in SML/CakeML rather than parsing this file.

(P A)
(P B)
(Q (P C))
!(match &self (P $x) $x)

(R A A)
(R A B)
!(match &self (R $x $x) $x)

(= (id $x) $x)
!(id A)
!(unknown A)
!(eval (unknown A))

!(chain (eval (id A)) $x (Pair $x B))
!(unify A A Good Bad)
!(unify A B Good Bad)
!(decons-atom (A B C))
!(cons-atom A (B C))
!(function (return A))

!(collapse (superpose (A B)))
!(let $x A (Pair $x B))
!(if True yes no)
!(+ 2 (* 3 4))
!(< 2 3)
!(+ 2 "x")

(= (loop) (loop))
!(loop)
