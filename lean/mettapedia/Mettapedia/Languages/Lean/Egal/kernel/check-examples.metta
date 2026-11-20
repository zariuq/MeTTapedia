; What the prover and the rule loader decide, shown on small goals: beside
; each goal that must be proved stands one that must not be.  Facts about
; numerals alone are settled by running their decision.  And two decisions
; computed: Lean's decision procedure for a bounded quantifier
; (Nat.decidableBallLT, under Nat.decidablePrime) is run by Lean's own
; equations, and it decides that 5 is prime and that 4 is not.
;
; check.sh runs (examples:report GROUP) for each group; a line is printed for
; each example, "example LABEL as-expected" or "example LABEL UNEXPECTED",
; and (examples:expected) lines are expected, all as expected.  Read after
; compute.metta.
(= (examples:expected) 19)

(= (examples:named $source) (Tm.named (lean:id $source)))
(= (examples:le $a $b) (Tm.app (Tm.app (examples:named "Lean_Nat_le_Prop") $a) $b))
(= (examples:succ $a) (Tm.app (examples:named "Lean_Nat_succ_node") $a))
(= (examples:num $k) (Tm.app (examples:named "LeanNum") (wire:literal $k)))
(= (examples:pi $X $F) (Tm.app (Tm.app (examples:named "Pi") $X) $F))
(= (examples:holds $P) (typ:member (examples:named "Empty") $P))
(= (examples:not-true $P) (Tm.imp (examples:holds $P) (examples:named "False")))
(= (examples:refutations $P) (examples:pi $P (Tm.lam (Tp.base 0) (examples:named "Lean_False_Prop"))))
; "n is prime", as Nat.decidablePrime states what it decides.
(= (examples:prime-number $n)
   (Tm.app (Tm.app (Tm.app (examples:named "Lean_Irreducible_Prop") (examples:named "Lean_Nat")) (examples:named "Lean_Nat_instMonoid"))
           (examples:num $n)))
; The context  x, x :e FIRST, h, h :e SECOND  (SECOND is written with x as
; the variable 0; in the goals x is the variable 1).
(= (examples:context $first $second)
   (let* (($th (lean:theory))
          ($c1 (mg:term-binder $th (mg:empty-context) (Tp.base 0)))
          ($c2 (mg:proof-binder $th $c1 (typ:member (Tm.db 0) $first)))
          ($c3 (mg:term-binder $th $c2 (Tp.base 0))))
     (mg:proof-binder $th $c3 (typ:member (Tm.db 0) (mgt:shift $second 1 0)))))
(= (examples:proved $ctx $goal) (not (== (typ:prove (lean:equality) $ctx () $goal) None)))
(= (examples:line $label $wanted $got)
   (println! (format-args "example {} {}" ($label (if (== $wanted $got) as-expected UNEXPECTED)))))
(= (examples:set-aside $name) (not (== (collapse (match &self (RuleSetAside $name) yes)) ())))

; decide (Nat.Prime n), as the reader writes test 27 for n = 97.
(= (examples:prime $n)
   (wire (app Decidable.decide ((app Irreducible ((app Nat ()) (app Nat.instMonoid ()) (num $n))) (app Nat.decidablePrime ((num $n)))))
         ()))
; The term is computed to VALUE by a theorem that states so, and that
; theorem is not taken as one for the other truth value.
(= (examples:decides $n $value $other $label $crossed)
   (let* (($E (lean:equality)) ($t (examples:prime $n)))
     (case (lean:compute $t)
       (((Conv $reached $theorem)
         (let* (($own (examples:line $label True
                        (if (== $reached $value) (== (mg:proposition $theorem) (eq:of $E $t $value)) False)))
                ($taken (collapse (mg:exact (eq:theory $E) (mg:empty-context) (eq:of $E $t $other) $theorem))))
           (examples:line $crossed False (not (== $taken ())))))
        ($stopped
         (let $own (examples:line $label True False) (examples:line $crossed False True)))))))

; The examples in four groups, each run by check.sh in a process of its own
; (a process keeps every term it has met, and what runs late in a long one
; pays for it).
(= (examples:groups) (goals five four settled))
(= (examples:report $group)
   (let $opened (lean:open-computation)
     (case $group
       ((goals (examples:goals))
        (five (examples:decides 5 (examples:named "Lean_Bool_true_node") (examples:named "Lean_Bool_false_node")
                                five-is-prime five-is-prime-crossed))
        (four (examples:decides 4 (examples:named "Lean_Bool_false_node") (examples:named "Lean_Bool_true_node")
                                four-is-not-prime four-is-not-prime-crossed))
        (settled (examples:settled))))))
(= (examples:goals)
   (let* (($nat (examples:named "Lean_Nat")) ($prop (examples:named "LeanProp"))
          ($x0 (Tm.db 0)) ($x (Tm.db 1))
          ; a product of propositions is a proposition; a product of numbers
          ; is not shown to be one
          ($a (examples:line product-of-propositions True
                (examples:proved (mg:empty-context)
                  (typ:member (examples:pi $nat (Tm.lam (Tp.base 0) (examples:le $x0 $x0))) $prop))))
          ($b (examples:line product-of-numbers False
                (examples:proved (mg:empty-context) (typ:member (examples:pi $nat (Tm.lam (Tp.base 0) $nat)) $prop))))
          ; every proof is 0: with h in a proposition, 0 is in it; with h in a
          ; type that is no proposition, nothing follows for 0
          ($c (examples:line proof-in-hand True
                (examples:proved (examples:context $nat (examples:le $x0 $x0)) (examples:holds (examples:le $x $x)))))
          ($d (examples:line member-of-a-type-in-hand False
                (examples:proved (examples:context $nat $nat) (examples:holds $nat))))
          ; a lemma after a view: succ x <= 4 gives succ x <= 5 once 5 is
          ; seen as succ 4; it does not give succ x <= 3
          ($e (examples:line order-step-after-view True
                (examples:proved (examples:context $nat (examples:le (examples:succ $x0) (examples:num 4)))
                                 (examples:holds (examples:le (examples:succ $x) (examples:num 5))))))
          ($f (examples:line order-step-downward False
                (examples:proved (examples:context $nat (examples:le (examples:succ $x0) (examples:num 4)))
                                 (examples:holds (examples:le (examples:succ $x) (examples:num 3))))))
          ; "p does not hold" from Lean's proof of not p in hand; without one
          ; it is not proved
          ($g (examples:line refuted-by-a-proof-in-hand True
                (examples:proved (examples:context $prop (examples:refutations $x0)) (examples:not-true $x))))
          ($h (examples:line refuted-with-nothing-in-hand False
                (examples:proved (examples:context $prop $nat) (examples:not-true $x))))
          ; the reading's stand-in definition is set aside; a definition that
          ; is Lean's is a rule
          ($i (examples:line stand-in-definition-set-aside True (examples:set-aside "Lean_Nat_decidableBallLT_unfold")))
          ($j (examples:line lean-definition-kept False (examples:set-aside "Lean_Nat_decidablePrime_unfold")))
          ; a fact about numerals alone is settled by running its decision:
          ; 1 <= 2 is proved and 3 <= 2 is not; under a binder the fact is
          ; the one proved before, read by its name
          ($m (examples:line order-between-numerals True
                (examples:proved (mg:empty-context) (examples:holds (examples:le (examples:num 1) (examples:num 2))))))
          ($n (examples:line false-order-between-numerals False
                (examples:proved (mg:empty-context) (examples:holds (examples:le (examples:num 3) (examples:num 2))))))
          ($o (examples:line order-between-numerals-under-a-binder True
                (examples:proved (examples:context $nat $nat) (examples:holds (examples:le (examples:num 1) (examples:num 2)))))))
     done))
; "3 is prime" is settled by the prover running Lean's decision procedure
; (a goal that the run itself asks for again is not started twice); "4 is
; prime" is refuted by it.
(= (examples:settled)
   (let* (($r (examples:line prime-settled-by-its-decision True
                (examples:proved (mg:empty-context) (examples:holds (examples:prime-number 3)))))
          ($s (examples:line composite-refuted-by-its-decision False
                (examples:proved (mg:empty-context) (examples:holds (examples:prime-number 4))))))
     done))
