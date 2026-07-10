; VerifiedMeTTa 03: reverse and reverse involution.

(= (listAppend Nil $ys) $ys)
(= (listAppend (Cons $x $xs) $ys) (Cons $x (listAppend $xs $ys)))

(= (rev Nil) Nil)
(= (rev (Cons $x $xs)) (listAppend (rev $xs) (Cons $x Nil)))

!(assertEqual
  (rev (Cons Z (Cons (S Z) (Cons (S (S Z)) Nil))))
  (Cons (S (S Z)) (Cons (S Z) (Cons Z Nil))))

!(assertEqual
  (rev (rev (Cons Z (Cons (S Z) (Cons (S (S Z)) Nil)))))
  (Cons Z (Cons (S Z) (Cons (S (S Z)) Nil))))
