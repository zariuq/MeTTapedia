; VerifiedMeTTa 01: Peano addition.

(= (add Z $n) $n)
(= (add (S $m) $n) (S (add $m $n)))

!(assertEqual (add Z (S Z)) (S Z))
!(assertEqual (add (S (S Z)) (S Z)) (S (S (S Z))))
!(assertEqual (add (S Z) (S (S Z))) (add (S (S Z)) (S Z)))
