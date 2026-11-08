;; The operations on natural numbers the target computes directly, with
;; Lean's conventions: subtraction stops at zero, division by zero is zero,
;; the remainder by zero is the dividend. Lean's own kernel computes the same
;; operations with GMP; every other operation runs by its equation theorems.

(= (Nat.add $a $b) (+ $a $b))
(= (Nat.sub $a $b) (if (< $a $b) 0 (- $a $b)))
(= (Nat.mul $a $b) (* $a $b))
(= (Nat.div $a $b) (if (== $b 0) 0 (/ (- $a (% $a $b)) $b)))
(= (Nat.mod $a $b) (if (== $b 0) $a (% $a $b)))
(= (Nat.pow $a $b) (lean-pow $a $b 1))
(= (lean-pow $a $b $acc)
   (if (== $b 0) $acc
       (if (== (% $b 2) 1)
           (lean-pow (* $a $a) (/ (- $b 1) 2) (* $acc $a))
           (lean-pow (* $a $a) (/ $b 2) $acc))))
(= (Nat.beq $a $b) (== $a $b))
(= (Nat.ble $a $b) (if (< $b $a) false true))
(= (Nat.decEq $a $b) (== $a $b))
(= (Nat.decLt $a $b) (< $a $b))
(= (Nat.decLe $a $b) (if (< $b $a) false true))
(= (Nat.succ $a) (+ $a 1))
(= (Nat.pred $a) (if (== $a 0) 0 (- $a 1)))

;; The recursor of the naturals by its two iota rules (the kernel's
;; definitional equations `Nat.rec z s 0 = z`, `Nat.rec z s (n+1) = s n (Nat.rec z s n)`).
(= (Nat.rec $z $s $n) (if (== $n 0) $z ($s (- $n 1) (Nat.rec $z $s (- $n 1)))))
