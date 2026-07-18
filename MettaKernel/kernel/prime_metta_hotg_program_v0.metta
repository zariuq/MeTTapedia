; =============================================================================
; prime_metta_hotg_program_v0.metta
;
; Calibration fixture connecting an actual MeTTa-Prime program to the generic
; inference checker.  Three independent presentations describe operational
; results, typing facts, and finite-set/HOTG judgments.  Runtime witnesses are
; translated explicitly into the three presentations before their certificates
; are replayed.
;
; This fixture establishes a checked differential for these finite examples.
; It does not establish evaluator correspondence, package adequacy, consistency,
; or a Megalodon correspondence theorem.
; =============================================================================

!(import! &self generic_inference_checker_v0)

; ---------- Actual MeTTa-Prime program --------------------------------------
(: Nat Type)
(: Bool Type)
(: Z Nat)
(: Truth Bool)

(= (pmh-choose) Z)
(= (pmh-choose) Truth)
(= (pmh-only) Z)

; Program mutations used to falsify the authored result-pair claim.
(= (pmh-choose-mut-removed) Z)
(= (pmh-choose-mut-replaced) Z)
(= (pmh-choose-mut-replaced) PMHUnexpected)

(= (pmh-choose-bag-agrees $observed)
   (case $observed
     ((($a $b)
        (if (== $a Z) (== $b Truth)
          (if (== $a Truth) (== $b Z) False)))
      ($_ False))))

; ---------- Stable finite-list constructors ---------------------------------
(= (pmh-l1 $a) (LCons $a LNil))
(= (pmh-l2 $a $b) (LCons $a (LCons $b LNil)))
(= (pmh-l3 $a $b $c) (LCons $a (LCons $b (LCons $c LNil))))
(= (pmh-l4 $a $b $c $d)
   (LCons $a (LCons $b (LCons $c (LCons $d LNil)))))
(= (pmh-l5 $a $b $c $d $e)
   (LCons $a (LCons $b (LCons $c (LCons $d (LCons $e LNil))))))
(= (pmh-pr1 $a) (PrCons $a PrNil))
(= (pmh-pr2 $a $b) (PrCons $a (PrCons $b PrNil)))

; ---------- Operational-result presentation --------------------------------
(= (pmh-eval-choose) (PApp "pmh.eval.choose" LNil))
(= (pmh-eval-only) (PApp "pmh.eval.only" LNil))
(= (pmh-eval-empty-program) (PApp "pmh.eval.empty-program" LNil))
(= (pmh-eval-Z) (PApp "pmh.eval.Z" LNil))
(= (pmh-eval-Truth) (PApp "pmh.eval.Truth" LNil))
(= (pmh-eval-pair $left $right)
   (PApp "pmh.eval.PairResults" (pmh-l2 $left $right)))
(= (pmh-eval-singleton $value)
   (PApp "pmh.eval.SingletonResults" (pmh-l1 $value)))
(= (pmh-eval-empty-results) (PApp "pmh.eval.EmptyResults" LNil))
(= (pmh-eval-branch $program $value)
   (PApp "pmh.eval.Branch" (pmh-l2 $program $value)))
(= (pmh-eval-complete $program $results)
   (PApp "pmh.eval.Complete" (pmh-l2 $program $results)))

(= (pmh-eval-rules)
   (gic-append
     (pmh-l3
       (GRule "pmh.eval.choose-z" LNil LNil
         (pmh-eval-branch (pmh-eval-choose) (pmh-eval-Z)))
       (GRule "pmh.eval.choose-truth" LNil LNil
         (pmh-eval-branch (pmh-eval-choose) (pmh-eval-Truth)))
       (GRule "pmh.eval.only-z" LNil LNil
         (pmh-eval-branch (pmh-eval-only) (pmh-eval-Z))))
     (pmh-l3
       (GRule "pmh.eval.complete-choose" LNil
         (pmh-l2
           (pmh-eval-branch (pmh-eval-choose) (pmh-eval-Z))
           (pmh-eval-branch (pmh-eval-choose) (pmh-eval-Truth)))
         (pmh-eval-complete
           (pmh-eval-choose)
           (pmh-eval-pair (pmh-eval-Z) (pmh-eval-Truth))))
       (GRule "pmh.eval.complete-only" LNil
         (pmh-l1 (pmh-eval-branch (pmh-eval-only) (pmh-eval-Z)))
         (pmh-eval-complete
           (pmh-eval-only) (pmh-eval-singleton (pmh-eval-Z))))
       (GRule "pmh.eval.complete-empty" LNil LNil
         (pmh-eval-complete
           (pmh-eval-empty-program) (pmh-eval-empty-results))))))

(= (pmh-eval-presentation)
   (GPresentation
     (gic-append
       (pmh-l4
         (CDecl "pmh.eval.choose" 0)
         (CDecl "pmh.eval.only" 0)
         (CDecl "pmh.eval.empty-program" 0)
         (CDecl "pmh.eval.Z" 0))
       (pmh-l4
         (CDecl "pmh.eval.Truth" 0)
         (CDecl "pmh.eval.PairResults" 2)
         (CDecl "pmh.eval.SingletonResults" 1)
         (CDecl "pmh.eval.EmptyResults" 0)))
     (pmh-l2
       (JDecl "pmh.eval.Branch" 2)
       (JDecl "pmh.eval.Complete" 2))
     (pmh-eval-rules)))

(= (pmh-eval-proof-choose-z)
   (GProof (GRuleInst "pmh.eval.choose-z" LNil) PrNil))
(= (pmh-eval-proof-choose-truth)
   (GProof (GRuleInst "pmh.eval.choose-truth" LNil) PrNil))
(= (pmh-eval-proof-only-z)
   (GProof (GRuleInst "pmh.eval.only-z" LNil) PrNil))
(= (pmh-eval-proof-complete-choose)
   (GProof
     (GRuleInst "pmh.eval.complete-choose" LNil)
     (pmh-pr2
       (pmh-eval-proof-choose-z)
       (pmh-eval-proof-choose-truth))))
(= (pmh-eval-proof-complete-only)
   (GProof
     (GRuleInst "pmh.eval.complete-only" LNil)
     (pmh-pr1 (pmh-eval-proof-only-z))))
(= (pmh-eval-proof-complete-empty)
   (GProof (GRuleInst "pmh.eval.complete-empty" LNil) PrNil))

(= (pmh-eval-goal-complete-choose)
   (pmh-eval-complete
     (pmh-eval-choose)
     (pmh-eval-pair (pmh-eval-Z) (pmh-eval-Truth))))
(= (pmh-eval-goal-complete-only)
   (pmh-eval-complete
     (pmh-eval-only) (pmh-eval-singleton (pmh-eval-Z))))
(= (pmh-eval-goal-complete-empty)
   (pmh-eval-complete
     (pmh-eval-empty-program) (pmh-eval-empty-results)))

; ---------- Independent typing presentation ---------------------------------
(= (pmh-type-Z) (PApp "pmh.type.Z" LNil))
(= (pmh-type-Truth) (PApp "pmh.type.Truth" LNil))
(= (pmh-type-Nat) (PApp "pmh.type.Nat" LNil))
(= (pmh-type-Bool) (PApp "pmh.type.Bool" LNil))
(= (pmh-type-has $term $type)
   (PApp "pmh.type.HasType" (pmh-l2 $term $type)))
(= (pmh-type-not-has $term $type)
   (PApp "pmh.type.NotHasType" (pmh-l2 $term $type)))

(= (pmh-type-rules)
   (pmh-l3
     (GRule "pmh.type.z-nat" LNil LNil
       (pmh-type-has (pmh-type-Z) (pmh-type-Nat)))
     (GRule "pmh.type.truth-bool" LNil LNil
       (pmh-type-has (pmh-type-Truth) (pmh-type-Bool)))
     (GRule "pmh.type.truth-not-nat" LNil LNil
       (pmh-type-not-has (pmh-type-Truth) (pmh-type-Nat)))))

(= (pmh-type-presentation)
   (GPresentation
     (pmh-l4
       (CDecl "pmh.type.Z" 0)
       (CDecl "pmh.type.Truth" 0)
       (CDecl "pmh.type.Nat" 0)
       (CDecl "pmh.type.Bool" 0))
     (pmh-l2
       (JDecl "pmh.type.HasType" 2)
       (JDecl "pmh.type.NotHasType" 2))
     (pmh-type-rules)))

(= (pmh-type-proof-z-nat)
   (GProof (GRuleInst "pmh.type.z-nat" LNil) PrNil))
(= (pmh-type-proof-truth-bool)
   (GProof (GRuleInst "pmh.type.truth-bool" LNil) PrNil))
(= (pmh-type-proof-truth-not-nat)
   (GProof (GRuleInst "pmh.type.truth-not-nat" LNil) PrNil))

; ---------- Finite-set/HOTG presentation ------------------------------------
; The result bag is treated extensionally inside this package.  Power and
; UnivOf use the exact rule shape of the Megalodon TG-universe fixture:
; UnivOf_Power N N (UnivOf_In N).
(= (pmh-hotg-Z) (PApp "pmh.hotg.Z" LNil))
(= (pmh-hotg-Truth) (PApp "pmh.hotg.Truth" LNil))
(= (pmh-hotg-Nat) (PApp "pmh.hotg.NatCarrier" LNil))
(= (pmh-hotg-pair $left $right)
   (PApp "pmh.hotg.PairResults" (pmh-l2 $left $right)))
(= (pmh-hotg-singleton $value)
   (PApp "pmh.hotg.SingletonResults" (pmh-l1 $value)))
(= (pmh-hotg-empty) (PApp "pmh.hotg.EmptyResults" LNil))
(= (pmh-hotg-Power $set) (PApp "pmh.hotg.Power" (pmh-l1 $set)))
(= (pmh-hotg-UnivOf $set) (PApp "pmh.hotg.UnivOf" (pmh-l1 $set)))
(= (pmh-hotg-In $element $set)
   (PApp "pmh.hotg.In" (pmh-l2 $element $set)))
(= (pmh-hotg-NotIn $element $set)
   (PApp "pmh.hotg.NotIn" (pmh-l2 $element $set)))
(= (pmh-hotg-Nonempty $set)
   (PApp "pmh.hotg.Nonempty" (pmh-l1 $set)))
(= (pmh-hotg-Subset $left $right)
   (PApp "pmh.hotg.Subset" (pmh-l2 $left $right)))
(= (pmh-hotg-NotSubset $left $right)
   (PApp "pmh.hotg.NotSubset" (pmh-l2 $left $right)))
(= (pmh-hotg-May $results $type-set)
   (PApp "pmh.hotg.May" (pmh-l2 $results $type-set)))
(= (pmh-hotg-Must $results $type-set)
   (PApp "pmh.hotg.Must" (pmh-l2 $results $type-set)))
(= (pmh-hotg-NotMust $results $type-set)
   (PApp "pmh.hotg.NotMust" (pmh-l2 $results $type-set)))
(= (pmh-hotg-rules)
   (gic-append
     (pmh-l5
       (GRule "pmh.hotg.in-pair-left"
         (pmh-l2 (Formal "x" 0) (Formal "y" 0)) LNil
         (pmh-hotg-In
           (FVar "x") (pmh-hotg-pair (FVar "x") (FVar "y"))))
       (GRule "pmh.hotg.in-pair-right"
         (pmh-l2 (Formal "x" 0) (Formal "y" 0)) LNil
         (pmh-hotg-In
           (FVar "y") (pmh-hotg-pair (FVar "x") (FVar "y"))))
       (GRule "pmh.hotg.in-singleton"
         (pmh-l1 (Formal "x" 0)) LNil
         (pmh-hotg-In (FVar "x") (pmh-hotg-singleton (FVar "x"))))
       (GRule "pmh.hotg.nat-z" LNil LNil
         (pmh-hotg-In (pmh-hotg-Z) (pmh-hotg-Nat)))
       (GRule "pmh.hotg.nat-not-truth" LNil LNil
         (pmh-hotg-NotIn (pmh-hotg-Truth) (pmh-hotg-Nat))))
     (gic-append
       (pmh-l5
         (GRule "pmh.hotg.nonempty"
           (pmh-l2 (Formal "x" 0) (Formal "R" 0))
           (pmh-l1 (pmh-hotg-In (FVar "x") (FVar "R")))
           (pmh-hotg-Nonempty (FVar "R")))
         (GRule "pmh.hotg.subset-singleton"
           (pmh-l2 (Formal "x" 0) (Formal "T" 0))
           (pmh-l1 (pmh-hotg-In (FVar "x") (FVar "T")))
           (pmh-hotg-Subset
             (pmh-hotg-singleton (FVar "x")) (FVar "T")))
         (GRule "pmh.hotg.not-subset"
           (pmh-l3
             (Formal "x" 0) (Formal "R" 0) (Formal "T" 0))
           (pmh-l2
             (pmh-hotg-In (FVar "x") (FVar "R"))
             (pmh-hotg-NotIn (FVar "x") (FVar "T")))
           (pmh-hotg-NotSubset (FVar "R") (FVar "T")))
         (GRule "pmh.hotg.may"
           (pmh-l3
             (Formal "x" 0) (Formal "R" 0) (Formal "T" 0))
           (pmh-l2
             (pmh-hotg-In (FVar "x") (FVar "R"))
             (pmh-hotg-In (FVar "x") (FVar "T")))
           (pmh-hotg-May (FVar "R") (FVar "T")))
         (GRule "pmh.hotg.must"
           (pmh-l2 (Formal "R" 0) (Formal "T" 0))
           (pmh-l2
             (pmh-hotg-Nonempty (FVar "R"))
             (pmh-hotg-Subset (FVar "R") (FVar "T")))
           (pmh-hotg-Must (FVar "R") (FVar "T"))))
       (pmh-l4
         (GRule "pmh.hotg.not-must"
           (pmh-l2 (Formal "R" 0) (Formal "T" 0))
           (pmh-l1 (pmh-hotg-NotSubset (FVar "R") (FVar "T")))
           (pmh-hotg-NotMust (FVar "R") (FVar "T")))
         (GRule "pmh.hotg.empty-not-must"
           (pmh-l1 (Formal "T" 0)) LNil
           (pmh-hotg-NotMust (pmh-hotg-empty) (FVar "T")))
         (GRule "pmh.hotg.univ-in"
           (pmh-l1 (Formal "X" 0)) LNil
           (pmh-hotg-In
             (FVar "X") (pmh-hotg-UnivOf (FVar "X"))))
         (GRule "pmh.hotg.univ-power"
           (pmh-l2 (Formal "N" 0) (Formal "X" 0))
           (pmh-l1
             (pmh-hotg-In
               (FVar "X") (pmh-hotg-UnivOf (FVar "N"))))
           (pmh-hotg-In
             (pmh-hotg-Power (FVar "X"))
             (pmh-hotg-UnivOf (FVar "N"))))))))

(= (pmh-hotg-constructors)
   (gic-append
     (pmh-l4
       (CDecl "pmh.hotg.Z" 0)
       (CDecl "pmh.hotg.Truth" 0)
       (CDecl "pmh.hotg.NatCarrier" 0)
       (CDecl "pmh.hotg.PairResults" 2))
     (pmh-l4
       (CDecl "pmh.hotg.SingletonResults" 1)
       (CDecl "pmh.hotg.EmptyResults" 0)
       (CDecl "pmh.hotg.Power" 1)
       (CDecl "pmh.hotg.UnivOf" 1))))

(= (pmh-hotg-judgments)
   (gic-append
     (pmh-l5
       (JDecl "pmh.hotg.In" 2)
       (JDecl "pmh.hotg.NotIn" 2)
       (JDecl "pmh.hotg.Nonempty" 1)
       (JDecl "pmh.hotg.Subset" 2)
       (JDecl "pmh.hotg.NotSubset" 2))
     (pmh-l3
       (JDecl "pmh.hotg.May" 2)
       (JDecl "pmh.hotg.Must" 2)
       (JDecl "pmh.hotg.NotMust" 2))))

(= (pmh-hotg-presentation)
   (GPresentation
     (pmh-hotg-constructors)
     (pmh-hotg-judgments)
     (pmh-hotg-rules)))

(= (pmh-hotg-presentation-missing-power)
   (GPresentation
     (gic-append
       (pmh-l4
         (CDecl "pmh.hotg.Z" 0)
         (CDecl "pmh.hotg.Truth" 0)
         (CDecl "pmh.hotg.NatCarrier" 0)
         (CDecl "pmh.hotg.PairResults" 2))
       (pmh-l3
         (CDecl "pmh.hotg.SingletonResults" 1)
         (CDecl "pmh.hotg.EmptyResults" 0)
         (CDecl "pmh.hotg.UnivOf" 1)))
     (pmh-hotg-judgments)
     (pmh-hotg-rules)))

; ---------- HOTG proof terms -------------------------------------------------
(= (pmh-hotg-result-pair)
   (pmh-hotg-pair (pmh-hotg-Z) (pmh-hotg-Truth)))
(= (pmh-hotg-result-singleton)
   (pmh-hotg-singleton (pmh-hotg-Z)))

(= (pmh-hotg-proof-pair-z)
   (GProof
     (GRuleInst "pmh.hotg.in-pair-left"
       (pmh-l2 (pmh-hotg-Z) (pmh-hotg-Truth))) PrNil))
(= (pmh-hotg-proof-pair-truth)
   (GProof
     (GRuleInst "pmh.hotg.in-pair-right"
       (pmh-l2 (pmh-hotg-Z) (pmh-hotg-Truth))) PrNil))
(= (pmh-hotg-proof-singleton-z)
   (GProof
     (GRuleInst "pmh.hotg.in-singleton" (pmh-l1 (pmh-hotg-Z))) PrNil))
(= (pmh-hotg-proof-nat-z)
   (GProof (GRuleInst "pmh.hotg.nat-z" LNil) PrNil))
(= (pmh-hotg-proof-nat-not-truth)
   (GProof (GRuleInst "pmh.hotg.nat-not-truth" LNil) PrNil))

(= (pmh-hotg-proof-nonempty-pair)
   (GProof
     (GRuleInst "pmh.hotg.nonempty"
       (pmh-l2 (pmh-hotg-Z) (pmh-hotg-result-pair)))
     (pmh-pr1 (pmh-hotg-proof-pair-z))))
(= (pmh-hotg-proof-nonempty-singleton)
   (GProof
     (GRuleInst "pmh.hotg.nonempty"
       (pmh-l2 (pmh-hotg-Z) (pmh-hotg-result-singleton)))
     (pmh-pr1 (pmh-hotg-proof-singleton-z))))
(= (pmh-hotg-proof-subset-singleton-nat)
   (GProof
     (GRuleInst "pmh.hotg.subset-singleton"
       (pmh-l2 (pmh-hotg-Z) (pmh-hotg-Nat)))
     (pmh-pr1 (pmh-hotg-proof-nat-z))))
(= (pmh-hotg-proof-not-subset-pair-nat)
   (GProof
     (GRuleInst "pmh.hotg.not-subset"
       (pmh-l3
         (pmh-hotg-Truth) (pmh-hotg-result-pair) (pmh-hotg-Nat)))
     (pmh-pr2
       (pmh-hotg-proof-pair-truth)
       (pmh-hotg-proof-nat-not-truth))))
(= (pmh-hotg-proof-may-pair-nat)
   (GProof
     (GRuleInst "pmh.hotg.may"
       (pmh-l3 (pmh-hotg-Z) (pmh-hotg-result-pair) (pmh-hotg-Nat)))
     (pmh-pr2 (pmh-hotg-proof-pair-z) (pmh-hotg-proof-nat-z))))
(= (pmh-hotg-proof-must-singleton-nat)
   (GProof
     (GRuleInst "pmh.hotg.must"
       (pmh-l2 (pmh-hotg-result-singleton) (pmh-hotg-Nat)))
     (pmh-pr2
       (pmh-hotg-proof-nonempty-singleton)
       (pmh-hotg-proof-subset-singleton-nat))))
(= (pmh-hotg-proof-not-must-pair-nat)
   (GProof
     (GRuleInst "pmh.hotg.not-must"
       (pmh-l2 (pmh-hotg-result-pair) (pmh-hotg-Nat)))
     (pmh-pr1 (pmh-hotg-proof-not-subset-pair-nat))))
(= (pmh-hotg-proof-empty-not-must-nat)
   (GProof
     (GRuleInst "pmh.hotg.empty-not-must" (pmh-l1 (pmh-hotg-Nat)))
     PrNil))
(= (pmh-hotg-proof-univ-in-result)
   (GProof
     (GRuleInst "pmh.hotg.univ-in" (pmh-l1 (pmh-hotg-result-pair)))
     PrNil))
(= (pmh-hotg-proof-power-result)
   (GProof
     (GRuleInst "pmh.hotg.univ-power"
       (pmh-l2
         (pmh-hotg-result-pair)
         (pmh-hotg-result-pair)))
     (pmh-pr1 (pmh-hotg-proof-univ-in-result))))

(= (pmh-hotg-goal-may-pair-nat)
   (pmh-hotg-May (pmh-hotg-result-pair) (pmh-hotg-Nat)))
(= (pmh-hotg-goal-not-must-pair-nat)
   (pmh-hotg-NotMust (pmh-hotg-result-pair) (pmh-hotg-Nat)))
(= (pmh-hotg-goal-must-singleton-nat)
   (pmh-hotg-Must (pmh-hotg-result-singleton) (pmh-hotg-Nat)))
(= (pmh-hotg-goal-empty-not-must-nat)
   (pmh-hotg-NotMust (pmh-hotg-empty) (pmh-hotg-Nat)))
(= (pmh-hotg-goal-power-result)
   (pmh-hotg-In
     (pmh-hotg-Power (pmh-hotg-result-pair))
     (pmh-hotg-UnivOf (pmh-hotg-result-pair))))

; ---------- Explicit bridges from runtime atoms -----------------------------
; A bridge relates representations; it grants no proof by itself.
; Judgment subjects are compared as quoted syntax.  Bare equality would run a
; nondeterministic subject again while attempting to authenticate it.
(= (pmh-bridge-runtime-value $value)
   (case $value
     ((Z
        (PMHValueBridge (pmh-eval-Z) (pmh-type-Z) (pmh-hotg-Z)))
      (Truth
        (PMHValueBridge
          (pmh-eval-Truth) (pmh-type-Truth) (pmh-hotg-Truth)))
      ($_ PMHNoValueBridge))))

(= (pmh-all2 $a $b) (if $a $b False))
(= (pmh-all3 $a $b $c) (if $a (if $b $c False) False))
(= (pmh-all4 $a $b $c $d)
   (if $a (if $b (if $c $d False) False) False))

; May is witnessed by the concrete runtime payload and then independently
; checked against the operational, typing, extensional, and universe packages.
(= (pmh-certify-choose-may
      (PrimeVerdict Established $judgment
        (MayWitness $index $payload Nat $edge)))
   (if (== (quote $judgment)
           (quote (May (PrimeEvaluate (pmh-choose)) Nat)))
     (case (pmh-bridge-runtime-value $payload)
       (((PMHValueBridge $eval-value $type-value $hotg-value)
         (if (== $eval-value (pmh-eval-Z))
           (if (== $type-value (pmh-type-Z))
             (if (== $hotg-value (pmh-hotg-Z))
               (pmh-all4
                 (gic-check
                   (pmh-eval-presentation)
                   (pmh-eval-goal-complete-choose)
                   (pmh-eval-proof-complete-choose))
                 (gic-check
                   (pmh-type-presentation)
                   (pmh-type-has (pmh-type-Z) (pmh-type-Nat))
                   (pmh-type-proof-z-nat))
                 (gic-check
                   (pmh-hotg-presentation)
                   (pmh-hotg-goal-may-pair-nat)
                   (pmh-hotg-proof-may-pair-nat))
                 (gic-check
                   (pmh-hotg-presentation)
                   (pmh-hotg-goal-power-result)
                   (pmh-hotg-proof-power-result)))
               False)
             False)
           False))
        ($_ False)))
     False))

; Refuted Must carries a concrete counterexample.  Its negative typing fact and
; the result set's failed-subset proof are checked in separate packages.
(= (pmh-certify-choose-not-must
      (PrimeVerdict Refuted $judgment
        (MustCounterexample $index $payload $detail)))
   (if (== (quote $judgment)
           (quote (Must (PrimeEvaluate (pmh-choose)) Nat)))
     (case (pmh-bridge-runtime-value $payload)
       (((PMHValueBridge $eval-value $type-value $hotg-value)
         (if (== $eval-value (pmh-eval-Truth))
           (if (== $type-value (pmh-type-Truth))
             (if (== $hotg-value (pmh-hotg-Truth))
               (pmh-all4
                 (gic-check
                   (pmh-eval-presentation)
                   (pmh-eval-goal-complete-choose)
                   (pmh-eval-proof-complete-choose))
                 (gic-check
                   (pmh-type-presentation)
                   (pmh-type-not-has
                     (pmh-type-Truth) (pmh-type-Nat))
                   (pmh-type-proof-truth-not-nat))
                 (gic-check
                   (pmh-hotg-presentation)
                   (pmh-hotg-goal-not-must-pair-nat)
                   (pmh-hotg-proof-not-must-pair-nat))
                 (gic-check
                   (pmh-hotg-presentation)
                   (pmh-hotg-goal-power-result)
                   (pmh-hotg-proof-power-result)))
               False)
             False)
           False))
        ($_ False)))
     False))

(= (pmh-certify-only-must
      (PrimeVerdict Established $judgment
        (MustEvidence 1 0 Complete
          (BranchEvidence 0 $payload $edge))))
   (if (== (quote $judgment)
           (quote (Must (PrimeEvaluate (pmh-only)) Nat)))
     (case (pmh-bridge-runtime-value $payload)
       (((PMHValueBridge $eval-value $type-value $hotg-value)
         (if (== $eval-value (pmh-eval-Z))
           (if (== $type-value (pmh-type-Z))
             (if (== $hotg-value (pmh-hotg-Z))
               (pmh-all3
                 (gic-check
                   (pmh-eval-presentation)
                   (pmh-eval-goal-complete-only)
                   (pmh-eval-proof-complete-only))
                 (gic-check
                   (pmh-type-presentation)
                   (pmh-type-has (pmh-type-Z) (pmh-type-Nat))
                   (pmh-type-proof-z-nat))
                 (gic-check
                   (pmh-hotg-presentation)
                   (pmh-hotg-goal-must-singleton-nat)
                   (pmh-hotg-proof-must-singleton-nat)))
               False)
             False)
           False))
        ($_ False)))
     False))

(= (pmh-certify-empty-not-must
      (PrimeVerdict Refuted $judgment (no-value-branches)))
   (if (== (quote $judgment)
           (quote (Must (PrimeEvaluate (superpose ())) Nat)))
     (pmh-all2
       (gic-check
         (pmh-eval-presentation)
         (pmh-eval-goal-complete-empty)
         (pmh-eval-proof-complete-empty))
       (gic-check
         (pmh-hotg-presentation)
         (pmh-hotg-goal-empty-not-must-nat)
         (pmh-hotg-proof-empty-not-must-nat)))
     False))

; ---------- Executable gates ------------------------------------------------
!(assertEqual (gic-presentation-valid (pmh-eval-presentation)) True)
!(assertEqual (gic-presentation-valid (pmh-type-presentation)) True)
!(assertEqual (gic-presentation-valid (pmh-hotg-presentation)) True)

!(assertEqual
   (gic-check
     (pmh-eval-presentation)
     (pmh-eval-goal-complete-choose)
     (pmh-eval-proof-complete-choose))
   True)
!(assertEqual
   (gic-check
     (pmh-eval-presentation)
     (pmh-eval-goal-complete-only)
     (pmh-eval-proof-complete-only))
   True)
!(assertEqual
   (gic-check
     (pmh-eval-presentation)
     (pmh-eval-goal-complete-empty)
     (pmh-eval-proof-complete-empty))
   True)

!(assertEqual
   (gic-check
     (pmh-type-presentation)
     (pmh-type-has (pmh-type-Z) (pmh-type-Nat))
     (pmh-type-proof-z-nat))
   True)
!(assertEqual
   (gic-check
     (pmh-type-presentation)
     (pmh-type-has (pmh-type-Truth) (pmh-type-Bool))
     (pmh-type-proof-truth-bool))
   True)
!(assertEqual
   (gic-check
     (pmh-type-presentation)
     (pmh-type-not-has (pmh-type-Truth) (pmh-type-Nat))
     (pmh-type-proof-truth-not-nat))
   True)

!(assertEqual
   (gic-check
     (pmh-hotg-presentation)
     (pmh-hotg-goal-may-pair-nat)
     (pmh-hotg-proof-may-pair-nat))
   True)
!(assertEqual
   (gic-check
     (pmh-hotg-presentation)
     (pmh-hotg-goal-not-must-pair-nat)
     (pmh-hotg-proof-not-must-pair-nat))
   True)
!(assertEqual
   (gic-check
     (pmh-hotg-presentation)
     (pmh-hotg-goal-must-singleton-nat)
     (pmh-hotg-proof-must-singleton-nat))
   True)
!(assertEqual
   (gic-check
     (pmh-hotg-presentation)
     (pmh-hotg-goal-empty-not-must-nat)
     (pmh-hotg-proof-empty-not-must-nat))
   True)
!(assertEqual
   (gic-check
     (pmh-hotg-presentation)
     (pmh-hotg-goal-power-result)
     (pmh-hotg-proof-power-result))
   True)

; Cross-package proofs and mutated claims are rejected.
!(assertEqual
   (gic-check
     (pmh-type-presentation)
     (pmh-type-has (pmh-type-Z) (pmh-type-Nat))
     (pmh-eval-proof-complete-choose))
   False)
!(assertEqual
   (gic-check
     (pmh-eval-presentation)
     (pmh-eval-goal-complete-choose)
     (pmh-hotg-proof-power-result))
   False)
!(assertEqual
   (gic-check
     (pmh-eval-presentation)
     (pmh-eval-complete
       (pmh-eval-choose) (pmh-eval-singleton (pmh-eval-Z)))
     (pmh-eval-proof-complete-choose))
   False)
!(assertEqual
   (gic-check
     (pmh-hotg-presentation)
     (pmh-hotg-Must (pmh-hotg-result-pair) (pmh-hotg-Nat))
     (pmh-hotg-proof-not-must-pair-nat))
   False)
!(assertEqual
   (gic-presentation-valid (pmh-hotg-presentation-missing-power))
   False)

; Actual Prime runtime verdicts are accepted only through all relevant checks.
; The authored two-answer result claim must agree with the live answer bag.
!(assertEqual (pmh-choose-bag-agrees (collapse (pmh-choose))) True)
!(assertEqual
   (pmh-choose-bag-agrees (collapse (pmh-choose-mut-removed))) False)
!(assertEqual
   (pmh-choose-bag-agrees (collapse (pmh-choose-mut-replaced))) False)

!(assertEqual
   (pmh-certify-choose-may
     (prime-judge &self
       (May (PrimeEvaluate (pmh-choose)) Nat)))
   True)
!(assertEqual
   (pmh-certify-choose-not-must
     (prime-judge &self
       (Must (PrimeEvaluate (pmh-choose)) Nat)))
   True)
!(assertEqual
   (pmh-certify-only-must
     (prime-judge &self
       (Must (PrimeEvaluate (pmh-only)) Nat)))
   True)
!(assertEqual
   (pmh-certify-empty-not-must
     (prime-judge &self
       (Must (PrimeEvaluate (superpose ())) Nat)))
   True)

; Plausible forged runtime evidence cannot cross the explicit value bridge.
!(assertEqual
   (pmh-certify-choose-may
     (PrimeVerdict Established
       (May (PrimeEvaluate PMHForgedChoose) Nat)
       (MayWitness 0 Truth Nat exact)))
   False)
!(assertEqual
   (pmh-certify-only-must
     (PrimeVerdict Established
       (Must (PrimeEvaluate PMHForgedOnly) Nat)
       (MustEvidence 1 0 Complete
         (BranchEvidence 0 Truth exact))))
   False)

; Correct evidence cannot be replayed against a forged subject judgment.
; Keep each forged subject inert so the negative tests syntax, not another run.
!(assertEqual
   (pmh-certify-choose-may
     (noeval (PrimeVerdict Established
       (May (PrimeEvaluate (pmh-only)) Nat)
       (MayWitness 0 Z Nat exact))))
   False)
!(assertEqual
   (pmh-certify-choose-not-must
     (noeval (PrimeVerdict Refuted
       (Must (PrimeEvaluate (pmh-only)) Nat)
       (MustCounterexample 1 Truth exact))))
   False)
!(assertEqual
   (pmh-certify-only-must
     (noeval (PrimeVerdict Established
       (Must (PrimeEvaluate (pmh-choose)) Nat)
       (MustEvidence 1 0 Complete
         (BranchEvidence 0 Z exact)))))
   False)
!(assertEqual
   (pmh-certify-empty-not-must
     (noeval (PrimeVerdict Refuted
       (Must (PrimeEvaluate (pmh-only)) Nat)
       (no-value-branches))))
   False)

!(println! (PrimeMettaHOTGProgramSummary 32 32 0))
