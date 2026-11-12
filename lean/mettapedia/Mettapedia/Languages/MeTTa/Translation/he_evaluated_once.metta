; A completed residual stays held after a later operation changes the space.
(= (g2 $x) (let $u (add-atom &self (= (later) done)) $x))
!(g2 (later))
; A fresh expression observes the newly stored equation.
!(later)
