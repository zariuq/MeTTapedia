; Atomic batch publication with a checked length and resumable work.
; This illustrates the execution contracts; the length guard here is an
; ordinary program, rather than a general dependent type checker.
!(import! &self (library lib_transform))

(= (qb:append Nil $ys) $ys)
(= (qb:append (Cons $x $xs) $ys)
   (let $tail (qb:append $xs $ys) (Cons $x $tail)))
(= (qb:length Nil) 0)
(= (qb:length (Cons $x $xs)) (+ 1 (qb:length $xs)))

(= (qb:checked $n $xs $answer)
   (if (== $n (qb:length $xs)) $answer (superpose ())))
(= (qb:reduce (Vec $n) (Append $xs $ys))
   (let $joined (qb:append $xs $ys)
     (qb:checked $n $joined (Value $joined))))
(= (qb:reduce (Vec $n) (Value $xs))
   (qb:checked $n $xs (CertifiedLength $n $xs)))

(= (qb:step $world $from $to)
   (collapse
     (transform $world
       (, (take (Active $from $type $expression))
          (absent (Active $to $other-type $other-expression))
          (let $reduct (qb:reduce $type $expression)))
       (Active $to $type $reduct) $world)))

(= (qb:drive Z $world $slot) (BudgetEnded $slot))
(= (qb:drive (S $fuel) $world $slot)
   (let $to (- 1 $slot)
     (let $answers (qb:step $world $slot $to)
       (if (== $answers ()) (Done $slot)
         (qb:drive $fuel $world $to)))))
(= (qb:view $world) (sort-atom (collapse (match $world $row $row))))

!(bind! &qb-world (new-space))
!(add-atom &qb-world
   (Active 0 (Vec 3) (Append (Cons 2 Nil) (Cons 3 (Cons 4 Nil)))))
!(qb:drive (S Z) &qb-world 0)
!(println! (BudgetKeepsValue
   (== (qb:view &qb-world) ((Active 1 (Vec 3) (Value (Cons 2 (Cons 3 (Cons 4 Nil)))))))))
!(qb:drive (S (S Z)) &qb-world 1)
!(println! (BatchCertified
   (== (qb:view &qb-world)
       ((Active 0 (Vec 3) (CertifiedLength 3 (Cons 2 (Cons 3 (Cons 4 Nil)))))))))
!(println! (OldSlotReused
   (== (collapse (match &qb-world (Active 1 $type $expression) occupied)) ())))
!(println! (ReplayRefused (== (qb:step &qb-world 0 1) ())))
!(println! (ReplayKeepsResult
   (== (qb:view &qb-world)
       ((Active 0 (Vec 3) (CertifiedLength 3 (Cons 2 (Cons 3 (Cons 4 Nil)))))))))

!(bind! &qb-wrong-length (new-space))
!(add-atom &qb-wrong-length
   (Active 0 (Vec 4) (Append (Cons 2 Nil) (Cons 3 (Cons 4 Nil)))))
!(println! (BadLengthRefused (== (qb:step &qb-wrong-length 0 1) ())))
!(println! (BadLengthKeepsRequest
   (== (qb:view &qb-wrong-length)
       ((Active 0 (Vec 4) (Append (Cons 2 Nil) (Cons 3 (Cons 4 Nil))))))))

!(bind! &qb-occupied (new-space))
!(add-atom &qb-occupied (Active 0 (Vec 0) (Append Nil Nil)))
!(add-atom &qb-occupied (Active 1 (Vec 0) (Value Nil)))
!(println! (OccupiedDestinationRefused (== (qb:step &qb-occupied 0 1) ())))
!(println! (OccupiedDestinationKeepsBoth
   (== (qb:view &qb-occupied)
       ((Active 0 (Vec 0) (Append Nil Nil)) (Active 1 (Vec 0) (Value Nil))))))
