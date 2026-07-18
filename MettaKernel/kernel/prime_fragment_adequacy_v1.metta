; =============================================================================
; prime_fragment_adequacy_v1.metta
;
; Executable source-to-package side of the bounded Prime fragment adequacy
; tranche.  The addition, length, and finite-pick packages imported below are
; all compiled from WexEquationV1/WexClosureV1 source declarations.  This file
; combines them, exercises the same proofs, and kills source/package/runtime
; misalignment mutations.  The corresponding two-way theorem is in Lean.
; =============================================================================

!(import! &self prime_raw_checking_worked_metta_programs_v0)
!(import! &self prime_package_identity_v1)

; ---------- One admitted fragment source and its derived package ------------
(= (pfa-canonical-source)
   (gic-append
     (wex1-source)
     (gic-append (wex2-source) (wex3-source))))

(= (pfa-package-from $source)
   (pmcp-package-v1 (wex-derive-source $source) LNil))

(= (pfa-canonical-package)
   (pfa-package-from (pfa-canonical-source)))

(= (pfa-cache-for $package)
   (case (pmcp-project-package $package)
     (((PMCPProjected $presentation) $presentation)
      ($_ (PFAProjectionRejectedV1)))))

(= (pfa-canonical-cache)
   (pfa-cache-for (pfa-canonical-package)))

; ---------- Source mutations ------------------------------------------------
(= (pfa-add-deleted-source)
   (pmcp-l1 (WexEquationV1 AddZeroV1)))

(= (pfa-pick-added-source)
   (pmcp-l4
     (WexEquationV1 PickAlternativeAV1)
     (WexEquationV1 PickAlternativeBV1)
     (WexEquationV1 PickAlternativeCV1)
     (WexClosureV1 MayEvalMembershipV1)))

(= (pfa-add-wrong-substitution-source)
   (pmcp-l2
     (WexEquationV1 AddZeroV1)
     (WexEquationV1 AddSuccessorWrongSubstitutionV1)))

(= (pfa-pick-duplicated-source)
   (pmcp-l4
     (WexEquationV1 PickAlternativeAV1)
     (WexEquationV1 PickAlternativeAV1)
     (WexEquationV1 PickAlternativeBV1)
     (WexClosureV1 MayEvalMembershipV1)))

(= (pfa-add-deleted-package)
   (pfa-package-from (pfa-add-deleted-source)))
(= (pfa-pick-added-package)
   (pfa-package-from (pfa-pick-added-source)))
(= (pfa-add-wrong-substitution-package)
   (pfa-package-from (pfa-add-wrong-substitution-source)))
(= (pfa-pick-duplicated-package)
   (pfa-package-from (pfa-pick-duplicated-source)))

; A deliberately hand-authored transcription is not accepted as the derived
; canonical package merely because it looks similar.
(= (pfa-hand-authored-package)
   (pmcp-package-v1
     (pmcp-l1
       (GRule "wex1.add-z" (pmcp-l1 (Formal "n" 0)) LNil
         (wex1-Evals
           (wex1-add-t (wex1-Z) (FVar "n")) (wex1-Z))))
     LNil))

; ---------- Mutation proofs and runtime observations ------------------------
(= (pfa-proof-pick-c)
   (GProof (GRuleInst "wex3.pick-c" LNil) PrNil))

(= (pfa-proof-add-one-one-wrong)
   (GProof
     (GRuleInst "wex1.add-s"
       (pmcp-l3 (wex1-Z) (wex1-one) (wex1-one)))
     (wex-pr1
       (GProof
         (GRuleInst "wex1.add-z" (pmcp-l1 (wex1-one))) PrNil))))

(= (pfa-goal-add-one-one-wrong)
   (wex1-Evals
     (wex1-add-t (wex1-one) (wex1-one)) (wex1-one)))

(= (pfa-observed-contains-c $observed)
   (case $observed
     (((PickC $b) True)
      (($a PickC) True)
      ((PickC $b $c) True)
      (($a PickC $c) True)
      (($a $b PickC) True)
      ($_ False))))

(= (pfa-mutant-branch-agrees $checked $observed)
   (if $checked (pfa-observed-contains-c $observed) False))

(= (pfa-wrong-add-agrees $checked $native)
   (if $checked
     (== (wex-encode-nat $native) (wex1-one))
     False))

(= (wex-pick-duplicated) PickA)
(= (wex-pick-duplicated) PickA)
(= (pfa-duplicate-bag-preserved $observed)
   (case $observed
     ((($a $b) (if (== $a PickA) (== $b PickA) False))
      ($_ False))))

(= (pfa-canonical-pick-bag $observed)
   (case $observed
     (((PickA PickB) True)
      ((PickB PickA) True)
      ($_ False))))

; ---------- Positive and falsifying gates ----------------------------------
!(assertEqual (pmcp-package-valid (pfa-canonical-package)) True)
!(assertEqual
   (pmcp-cache-valid (pfa-canonical-package) (pfa-canonical-cache)) True)
!(assertEqual
   (pmcp-check-reference
     (pfa-canonical-package) (wex1-goal) (wex1-proof-2))
   True)
!(assertEqual
   (pmcp-check-reference
     (pfa-canonical-package) (wex2-goal) (wex2-proof-ab))
   True)
!(assertEqual
   (pmcp-check-reference
     (pfa-canonical-package)
     (wex3-in-goal (wex3-A)) (wex3-in-a))
   True)

; Deleting the successor equation kills the existing addition derivation.
!(assertEqual
   (pmcp-check-reference
     (pfa-add-deleted-package) (wex1-goal) (wex1-proof-2))
   False)
!(assertEqual
   (== (ppi-package-identity (pfa-canonical-package))
       (ppi-package-identity (pfa-add-deleted-package)))
   False)

; Adding a source branch derives a real rule, but the unchanged native program
; does not return that branch, so the adequacy comparison fails closed.
!(assertEqual
   (pmcp-check-reference
     (pfa-pick-added-package)
     (wex3-MayEval (wex3-pick-t) (wex3-C)) (pfa-proof-pick-c))
   True)
!(assertEqual (pfa-observed-contains-c (collapse (wex-pick))) False)
!(assertEqual
   (pfa-mutant-branch-agrees
     (pmcp-check-reference
       (pfa-pick-added-package)
       (wex3-MayEval (wex3-pick-t) (wex3-C)) (pfa-proof-pick-c))
     (collapse (wex-pick)))
   False)

; A wrong substitution is accepted only by its mutated source package and is
; rejected by comparison with the native result.
!(assertEqual
   (pmcp-check-reference
     (pfa-add-wrong-substitution-package)
     (pfa-goal-add-one-one-wrong) (pfa-proof-add-one-one-wrong))
   True)
!(assertEqual
   (== (wex-encode-nat (wex-add (NS NZ) (NS NZ))) (wex1-one))
   False)
!(assertEqual
   (pfa-wrong-add-agrees
     (pmcp-check-reference
       (pfa-add-wrong-substitution-package)
       (pfa-goal-add-one-one-wrong) (pfa-proof-add-one-one-wrong))
     (wex-add (NS NZ) (NS NZ)))
   False)

; Bag multiplicity is observed, not silently quotiented into a set.  The
; duplicate source package is independently inadmissible because rule IDs must
; also remain unique.
!(assertEqual
   (pfa-duplicate-bag-preserved (collapse (wex-pick-duplicated))) True)
!(assertEqual (pfa-canonical-pick-bag (collapse (wex-pick-duplicated))) False)
!(assertEqual (pmcp-package-valid (pfa-pick-duplicated-package)) False)

!(assertEqual
   (== (pfa-hand-authored-package) (pfa-canonical-package)) False)
!(assertEqual
   (== (ppi-package-identity (pfa-hand-authored-package))
       (ppi-package-identity (pfa-canonical-package)))
   False)

!(println! "PRIME_FRAGMENT_PACKAGE_CANONICAL_BEGIN")
!(println! (ppi-canonical-bytes (pfa-canonical-package)))
!(println! "PRIME_FRAGMENT_PACKAGE_CANONICAL_END")
!(println! (PrimeFragmentAdequacyMeTTaSummaryV1 18 18 0))
