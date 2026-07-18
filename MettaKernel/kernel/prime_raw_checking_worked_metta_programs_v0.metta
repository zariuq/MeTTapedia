; =============================================================================
; prime_raw_checking_worked_metta_programs_v0.metta
;
; Worked examples: an OBJECT-LOGIC-NEUTRAL checker consuming ACTUAL MeTTa
; programs.  (Neutral, not "logic-free": every judgment gets its meaning from
; a hand-authored package; the checker itself privileges none of them.)
;
; Three ordinary MeTTa programs run natively in this file (Peano addition,
; list length, a nondeterministic picker).  Each also gets a rules-only
; package in the prime_minimal_checking_package_v0 format, and certificates
; about concrete runs are replayed by the ONE generic checker.  Encoder
; functions bridge native results to certified value patterns, so the
; certificate's claim is compared against what the program actually computes.
; W3's answer bag is OBSERVED via collapse, and two program mutants (a branch
; removed; a branch replaced) must each disagree with the certified set.
;
; The third example layers a set-membership judgment over the operational
; may-evaluate judgment: membership facts about a live nondeterministic
; program's result set, checked by the same package-neutral checker.
;
; Scope: package-relative certificate replay plus native-result agreement on
; the exercised runs.  The packages transcribe the defining equations; no
; adequacy theorem to full MeTTa evaluation, no consistency, no truth, no
; parsing is claimed.  The checker and the pmcp package format are imported
; unchanged; this file adds only packages, certificates, and assertions.
; The gate also checks a manually aligned extensional graph for W1 with the
; independent Megalodon checker.  That differential is not a translation or
; an evaluator-adequacy theorem.
; =============================================================================

!(import! &self prime_minimal_checking_package_v0)

; ---------- Shared small helpers --------------------------------------------
(= (wex-pr1 $a) (PrCons $a PrNil))

; =============================================================================
; W1. Peano addition — the program
; =============================================================================
(= (wex-add NZ $n) $n)
(= (wex-add (NS $m) $n) (NS (wex-add $m $n)))

; Pattern-side constructors and encoder (the native<->pattern bridge).
(= (wex1-Z) (PApp "wex.Z" LNil))
(= (wex1-S $n) (PApp "wex.S" (pmcp-l1 $n)))
(= (wex1-add-t $m $n) (PApp "wex.add" (pmcp-l2 $m $n)))
(= (wex1-Evals $e $v) (PApp "wex1.Evals" (pmcp-l2 $e $v)))

(= (wex-encode-nat NZ) (wex1-Z))
(= (wex-encode-nat (NS $n)) (wex1-S (wex-encode-nat $n)))

(= (wex1-one) (wex1-S (wex1-Z)))
(= (wex1-two) (wex1-S (wex1-one)))
(= (wex1-three) (wex1-S (wex1-two)))
(= (wex1-four) (wex1-S (wex1-three)))

; The rule list is derived later from these admitted equation tags.
(= (wex1-source)
   (pmcp-l2
     (WexEquationV1 AddZeroV1)
     (WexEquationV1 AddSuccessorV1)))
(= (wex1-rules) (wex-derive-source (wex1-source)))
(= (wex1-package) (pmcp-package-v1 (wex1-rules) LNil))

; Independently written expected projection (first-occurrence order).
(= (wex1-cache)
   (GPresentation
     (pmcp-l3
       (CDecl "wex.add" 2)
       (CDecl "wex.Z" 0)
       (CDecl "wex.S" 1))
     (pmcp-l1 (JDecl "wex1.Evals" 2))
     (wex1-rules)))

; Certificate for the concrete run: add 2 1 = 3.
(= (wex1-proof-0)
   (GProof (GRuleInst "wex1.add-z" (pmcp-l1 (wex1-one))) PrNil))
(= (wex1-proof-1)
   (GProof
     (GRuleInst "wex1.add-s"
       (pmcp-l3 (wex1-Z) (wex1-one) (wex1-one)))
     (wex-pr1 (wex1-proof-0))))
(= (wex1-proof-2)
   (GProof
     (GRuleInst "wex1.add-s"
       (pmcp-l3 (wex1-S (wex1-Z)) (wex1-one) (wex1-S (wex1-one))))
     (wex-pr1 (wex1-proof-1))))
(= (wex1-goal)
   (wex1-Evals (wex1-add-t (wex1-two) (wex1-one)) (wex1-three)))
(= (wex1-wrong-goal)
   (wex1-Evals (wex1-add-t (wex1-two) (wex1-one)) (wex1-four)))
(= (wex1-skipped-proof)
   (GProof
     (GRuleInst "wex1.add-s"
       (pmcp-l3 (wex1-S (wex1-Z)) (wex1-one) (wex1-S (wex1-one))))
     PrNil))

; =============================================================================
; W2. List length — a second program, same checker, only data differs
; =============================================================================
(= (wex-len WNil) NZ)
(= (wex-len (WCons $h $t)) (NS (wex-len $t)))

(= (wex2-Nil) (PApp "wex.Nil" LNil))
(= (wex2-Cons $h $t) (PApp "wex.Cons" (pmcp-l2 $h $t)))
(= (wex2-a) (PApp "wex.a" LNil))
(= (wex2-b) (PApp "wex.b" LNil))
(= (wex2-LenIs $l $n) (PApp "wex2.LenIs" (pmcp-l2 $l $n)))

(= (wex-encode-item ItemA) (wex2-a))
(= (wex-encode-item ItemB) (wex2-b))
(= (wex-encode-list WNil) (wex2-Nil))
(= (wex-encode-list (WCons $h $t))
   (wex2-Cons (wex-encode-item $h) (wex-encode-list $t)))

(= (wex2-source)
   (pmcp-l2
     (WexEquationV1 LengthNilV1)
     (WexEquationV1 LengthConsV1)))
(= (wex2-rules) (wex-derive-source (wex2-source)))
(= (wex2-package) (pmcp-package-v1 (wex2-rules) LNil))

(= (wex2-list-ab) (wex2-Cons (wex2-a) (wex2-Cons (wex2-b) (wex2-Nil))))
(= (wex2-proof-nil)
   (GProof (GRuleInst "wex2.len-nil" LNil) PrNil))
(= (wex2-proof-b)
   (GProof
     (GRuleInst "wex2.len-cons"
       (pmcp-l3 (wex2-b) (wex2-Nil) (wex1-Z)))
     (wex-pr1 (wex2-proof-nil))))
(= (wex2-proof-ab)
   (GProof
     (GRuleInst "wex2.len-cons"
       (pmcp-l3 (wex2-a) (wex2-Cons (wex2-b) (wex2-Nil)) (wex1-one)))
     (wex-pr1 (wex2-proof-b))))
(= (wex2-goal) (wex2-LenIs (wex2-list-ab) (wex1-two)))

; =============================================================================
; W3. Nondeterministic picker — set-membership judgments about a live program
; =============================================================================
(: WexPickAType Type)
(: WexPickBType Type)
(: PickA WexPickAType)
(: PickB WexPickBType)
(: PickC WexPickBType)

(= (wex-pick) PickA)
(= (wex-pick) PickB)

(= (wex3-pick-t) (PApp "wex.pick" LNil))
(= (wex3-A) (PApp "wex.A" LNil))
(= (wex3-B) (PApp "wex.B" LNil))
(= (wex3-C) (PApp "wex.C" LNil))
(= (wex3-ResultSet $e) (PApp "wex.ResultSet" (pmcp-l1 $e)))
(= (wex3-MayEval $e $v) (PApp "wex3.MayEval" (pmcp-l2 $e $v)))
(= (wex3-In $x $s) (PApp "wex3.In" (pmcp-l2 $x $s)))

(= (wex-encode-pick PickA) (wex3-A))
(= (wex-encode-pick PickB) (wex3-B))

; Program mutants for the runtime differential: one branch removed, one
; branch replaced.  The observed answer bag of each mutant must DISAGREE
; with the certified result set {PickA, PickB}.
(= (wex-pick-mut-removed) PickA)
(= (wex-pick-mut-replaced) PickA)
(= (wex-pick-mut-replaced) PickC)

; Observed-answer-bag agreement with the certified set, order-insensitive.
; Anything other than exactly {PickA, PickB} is False (fail-closed).
(= (wex3-agrees $observed)
   (case $observed
     ((($a $b)
        (if (== $a PickA) (== $b PickB)
          (if (== $a PickB) (== $b PickA) False)))
      ($_ False))))

; Every OBSERVED runtime answer must have a checking certificate.  A value
; with no certificate (the replaced-branch mutant's PickC) is False.
(= (wex3-certify-one $result)
   (case $result
     ((PickA (pmcp-check-reference
               (wex3-package)
               (wex3-MayEval (wex3-pick-t) (wex3-A)) (wex3-may-a)))
      (PickB (pmcp-check-reference
               (wex3-package)
               (wex3-MayEval (wex3-pick-t) (wex3-B)) (wex3-may-b)))
      ($_ False))))
(= (wex3-certify-observed $observed)
   (case $observed
     ((($a $b) (if (wex3-certify-one $a) (wex3-certify-one $b) False))
      (($a) (wex3-certify-one $a))
      ($_ False))))

; ---------- Source-to-package compiler -------------------------------------
; Equations are authoritative program declarations.  The membership closure
; is named separately because it is an inference layer, not a program
; equation.  Every package below is obtained by this one deterministic map.
(= (wex-derive-declaration (WexEquationV1 AddZeroV1))
   (GRule "wex1.add-z" (pmcp-l1 (Formal "n" 0)) LNil
     (wex1-Evals (wex1-add-t (wex1-Z) (FVar "n")) (FVar "n"))))

(= (wex-derive-declaration (WexEquationV1 AddSuccessorV1))
   (GRule "wex1.add-s"
     (pmcp-l3 (Formal "m" 0) (Formal "n" 0) (Formal "v" 0))
     (pmcp-l1
       (wex1-Evals (wex1-add-t (FVar "m") (FVar "n")) (FVar "v")))
     (wex1-Evals
       (wex1-add-t (wex1-S (FVar "m")) (FVar "n"))
       (wex1-S (FVar "v")))))

(= (wex-derive-declaration (WexEquationV1 LengthNilV1))
   (GRule "wex2.len-nil" LNil LNil
     (wex2-LenIs (wex2-Nil) (wex1-Z))))

(= (wex-derive-declaration (WexEquationV1 LengthConsV1))
   (GRule "wex2.len-cons"
     (pmcp-l3 (Formal "h" 0) (Formal "t" 0) (Formal "v" 0))
     (pmcp-l1 (wex2-LenIs (FVar "t") (FVar "v")))
     (wex2-LenIs
       (wex2-Cons (FVar "h") (FVar "t"))
       (wex1-S (FVar "v")))))

(= (wex-derive-declaration (WexEquationV1 PickAlternativeAV1))
   (GRule "wex3.pick-a" LNil LNil
     (wex3-MayEval (wex3-pick-t) (wex3-A))))

(= (wex-derive-declaration (WexEquationV1 PickAlternativeBV1))
   (GRule "wex3.pick-b" LNil LNil
     (wex3-MayEval (wex3-pick-t) (wex3-B))))

; Mutation-only declarations are compiled by the same mechanism.
(= (wex-derive-declaration (WexEquationV1 PickAlternativeCV1))
   (GRule "wex3.pick-c" LNil LNil
     (wex3-MayEval (wex3-pick-t) (wex3-C))))
(= (wex-derive-declaration (WexEquationV1 AddSuccessorWrongSubstitutionV1))
   (GRule "wex1.add-s"
     (pmcp-l3 (Formal "m" 0) (Formal "n" 0) (Formal "v" 0))
     (pmcp-l1
       (wex1-Evals (wex1-add-t (FVar "m") (FVar "n")) (FVar "v")))
     (wex1-Evals
       (wex1-add-t (wex1-S (FVar "m")) (FVar "n"))
       (wex1-S (FVar "m")))))

(= (wex-derive-declaration (WexClosureV1 MayEvalMembershipV1))
   (GRule "wex3.mayeval-in"
     (pmcp-l1 (Formal "x" 0))
     (pmcp-l1 (wex3-MayEval (wex3-pick-t) (FVar "x")))
     (wex3-In (FVar "x") (wex3-ResultSet (wex3-pick-t)))))

(= (wex-derive-source LNil) LNil)
(= (wex-derive-source (LCons $declaration $rest))
   (LCons
     (wex-derive-declaration $declaration)
     (wex-derive-source $rest)))

(= (wex3-source)
   (pmcp-l3
     (WexEquationV1 PickAlternativeAV1)
     (WexEquationV1 PickAlternativeBV1)
     (WexClosureV1 MayEvalMembershipV1)))
(= (wex3-rules) (wex-derive-source (wex3-source)))
(= (wex3-package) (pmcp-package-v1 (wex3-rules) LNil))

(= (wex3-may-a)
   (GProof (GRuleInst "wex3.pick-a" LNil) PrNil))
(= (wex3-may-b)
   (GProof (GRuleInst "wex3.pick-b" LNil) PrNil))
(= (wex3-in-a)
   (GProof
     (GRuleInst "wex3.mayeval-in" (pmcp-l1 (wex3-A)))
     (wex-pr1 (wex3-may-a))))
(= (wex3-in-b)
   (GProof
     (GRuleInst "wex3.mayeval-in" (pmcp-l1 (wex3-B)))
     (wex-pr1 (wex3-may-b))))
(= (wex3-in-c-forged)
   (GProof
     (GRuleInst "wex3.mayeval-in" (pmcp-l1 (wex3-C)))
     (wex-pr1 (wex3-may-a))))
(= (wex3-in-goal $x)
   (wex3-In $x (wex3-ResultSet (wex3-pick-t))))

; Prime's native May/Must judgments remain untrusted evidence until the
; payload is replayed against this example's independently authored package.
; Destructure verdicts without evaluating their stored subjects, then compare
; quoted judgments: bare equality would run the nondeterministic program again.
(= (wex3-check-prime-may $verdict)
   (case (noeval $verdict)
     (((PrimeVerdict Established $judgment
         (MayWitness $index PickA WexPickAType $edge))
       (if (== (quote $judgment)
             (quote (May (PrimeEvaluate (wex-pick)) WexPickAType)))
         (pmcp-check-reference
           (wex3-package) (wex3-in-goal (wex3-A)) (wex3-in-a))
         False))
      ($_ False))))

(= (wex3-check-prime-not-must $verdict)
   (case (noeval $verdict)
     (((PrimeVerdict Refuted $judgment
         (MustCounterexample $index PickB $detail))
       (if (== (quote $judgment)
             (quote (Must (PrimeEvaluate (wex-pick)) WexPickAType)))
         (pmcp-check-reference
           (wex3-package) (wex3-in-goal (wex3-B)) (wex3-in-b))
         False))
      ($_ False))))

; =============================================================================
; Executable gates
; =============================================================================
; --- W1: Peano addition ---
!(assertEqual
   (pmcp-project-rules (wex1-rules))
   (PMCPProjected (wex1-cache)))
!(assertEqual (pmcp-package-valid (wex1-package)) True)
!(assertEqual (pmcp-cache-valid (wex1-package) (wex1-cache)) True)
!(assertEqual
   (pmcp-check-reference (wex1-package) (wex1-goal) (wex1-proof-2))
   True)
!(assertEqual
   (pmcp-check-cached
     (wex1-package) (wex1-cache) (wex1-goal) (wex1-proof-2))
   True)
; The certified value equals what the native program actually computes.
!(assertEqual
   (wex-encode-nat (wex-add (NS (NS NZ)) (NS NZ)))
   (wex1-three))
!(assertEqual
   (pmcp-check-reference (wex1-package) (wex1-wrong-goal) (wex1-proof-2))
   False)
!(assertEqual
   (pmcp-check-reference (wex1-package) (wex1-goal) (wex1-skipped-proof))
   False)

; --- W2: list length ---
!(assertEqual (pmcp-package-valid (wex2-package)) True)
!(assertEqual
   (pmcp-check-reference (wex2-package) (wex2-goal) (wex2-proof-ab))
   True)
!(assertEqual
   (wex-encode-nat (wex-len (WCons ItemA (WCons ItemB WNil))))
   (wex1-two))
!(assertEqual
   (wex-encode-list (WCons ItemA (WCons ItemB WNil)))
   (wex2-list-ab))
!(assertEqual
   (pmcp-check-reference (wex2-package) (wex2-goal) (wex1-proof-2))
   False)

; --- W3: nondeterministic picker with set-membership layer ---
!(assertEqual (pmcp-package-valid (wex3-package)) True)
!(assertEqual
   (pmcp-check-reference
     (wex3-package)
     (wex3-MayEval (wex3-pick-t) (wex3-A)) (wex3-may-a))
   True)
!(assertEqual
   (pmcp-check-reference
     (wex3-package) (wex3-in-goal (wex3-A)) (wex3-in-a))
   True)
!(assertEqual
   (pmcp-check-reference
     (wex3-package) (wex3-in-goal (wex3-B)) (wex3-in-b))
   True)
!(assertEqual
   (pmcp-check-reference
     (wex3-package) (wex3-in-goal (wex3-C)) (wex3-in-c-forged))
   False)
; Each certified value is the encoding of a value the program can return.
!(assertEqual (wex-encode-pick PickA) (wex3-A))
!(assertEqual (wex-encode-pick PickB) (wex3-B))
!(assertEqual
   (pmcp-check-reference (wex1-package) (wex3-in-goal (wex3-A)) (wex3-in-a))
   False)

; --- W3 live runtime differential: the program actually runs ---
!(assertEqual (wex3-agrees (collapse (wex-pick))) True)
!(assertEqual (wex3-agrees (collapse (wex-pick-mut-removed))) False)
!(assertEqual (wex3-agrees (collapse (wex-pick-mut-replaced))) False)
!(assertEqual (wex3-certify-observed (collapse (wex-pick))) True)
!(assertEqual (wex3-certify-observed (collapse (wex-pick-mut-replaced))) False)

; --- W3 Prime-native judgment bridge ---
; The actual nondeterministic program supplies both the positive May witness
; and the negative Must counterexample.  Both are independently replayed.
!(assertEqual
   (unique
     (wex3-check-prime-may
       (prime-judge &self
         (May (PrimeEvaluate (wex-pick)) WexPickAType))))
   True)
!(assertEqual
   (unique
     (wex3-check-prime-not-must
       (prime-judge &self
         (Must (PrimeEvaluate (wex-pick)) WexPickAType))))
   True)
; Plausible evidence with the wrong runtime payload cannot cross the bridge.
!(assertEqual
   (wex3-check-prime-may
     (PrimeVerdict Established WexForgedMayQuery
       (MayWitness 0 PickB WexPickAType exact)))
   False)
!(assertEqual
   (wex3-check-prime-not-must
     (PrimeVerdict Refuted WexForgedMustQuery
       (MustCounterexample 0 PickA exact)))
   False)
; Correct evidence about the wrong subject is still a forgery.
!(assertEqual
   (wex3-check-prime-may
     (PrimeVerdict Established WexWrongSubjectMay
       (MayWitness 0 PickA WexPickAType exact)))
   False)
!(assertEqual
   (wex3-check-prime-not-must
     (PrimeVerdict Refuted WexWrongSubjectMust
       (MustCounterexample 1 PickB exact)))
   False)

!(println! (PrimeWorkedMettaProgramsSummary 32 32 0))
