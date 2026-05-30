; Broad HE-style capacity prototypes.
; These are intentionally easy witnesses, not a full parser input suite yet.

; 1. Parser/top-level witness
(P A)
!(match &self (P $x) $x)

; 2. Pure atom/matching/substitution
(R A A)
(R A B)
!(match &self (R $x $x) $x)

; 3. Equality-driven evaluation
(= (id $x) $x)
!(id A)

; 4. Minimal instruction subset
!(chain (eval (id A)) $x (Pair $x B))
!(unify A A Good Bad)
!(decons-atom (A B C))
!(cons-atom A (B C))
!(function (return A))

; 5. Meta-type/evaluation-order witness
(= (x) A)
(: hold (-> Atom Atom))
(= (hold $a) $a)
!(hold (x))

; 6. Type witness
(: Nat Type)
(: Z Nat)
(: S (-> Nat Nat))
(: Add (-> Nat Nat Nat))
(= (Add $x Z) $x)
!(Add Z Z)

; 7. Effects boundary: spaces
!(bind! &kb (new-space))
!(add-atom &kb (P A))
!(match &kb (P $x) $x)

; 8. Effects boundary: states
!(bind! &s (new-state off))
!(get-state &s)
!(change-state! &s on)
!(get-state &s)

; 9. Modules/imports and open primitive boundary
; Keep call-native outside the verified kernel. Use finite primitive table
; witnesses first, then deterministic module import witnesses.
!(import! &self moduleA)
!(f 2)
