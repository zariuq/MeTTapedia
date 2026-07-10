; VerifiedMeTTa 02: list append and length.

(= (listAppend Nil $ys) $ys)
(= (listAppend (Cons $x $xs) $ys) (Cons $x (listAppend $xs $ys)))

(= (len Nil) Z)
(= (len (Cons $x $xs)) (S (len $xs)))

!(assertEqual
  (listAppend (Cons Z (Cons (S Z) Nil)) (Cons (S (S Z)) Nil))
  (Cons Z (Cons (S Z) (Cons (S (S Z)) Nil))))

!(assertEqual
  (len (listAppend (Cons Z (Cons (S Z) Nil)) (Cons (S (S Z)) Nil)))
  (S (S (S Z))))
