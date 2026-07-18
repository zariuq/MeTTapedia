; =============================================================================
; prime_subject_ref_v1.metta
;
; Phase-2 calibration for subject-indexed Prime certificates.  A SubjectRefV1
; commits to inert program syntax, the exact admitted checking package, the
; runtime Prime identity, a checked space manifest and temporal revision, the
; runtime judgment, the checked judgment, and explicit conversion/effect
; policies.  Runtime occurrence identity is deliberately separate.
;
; The generic checker is imported unchanged.  Runtime observations remain
; evidence; only replay of the indexed generic derivation grants Checked.
; =============================================================================

!(import! &self prime_package_identity_v1)
!(import! &self prime_metta_hotg_program_v0)

; ---------- A dedicated, exactly manifested Prime program space ------------
(= (psr-l7 $a $b $c $d $e $f $g)
   (LCons $a
     (LCons $b
       (LCons $c
         (LCons $d
           (LCons $e
             (LCons $f (LCons $g LNil))))))))

(= (psr-environment-manifest)
   (psr-l7
     "(: Nat Type)"
     "(: Bool Type)"
     "(: Z Nat)"
     "(: Truth Bool)"
     "(= (pmh-choose) Z)"
     "(= (pmh-choose) Truth)"
     "(= (pmh-only) Z)"))

(= (psr-load-environment $space)
   (let $_a (add-atom $space (: Nat Type))
     (let $_b (add-atom $space (: Bool Type))
       (let $_c (add-atom $space (: Z Nat))
         (let $_d (add-atom $space (: Truth Bool))
           (let $_e (add-atom $space (= (pmh-choose) Z))
             (let $_f (add-atom $space (= (pmh-choose) Truth))
               (add-atom $space (= (pmh-only) Z)))))))))

!(bind! &psr-env (new-space))
!(psr-load-environment &psr-env)
!(bind! &psr-env-mutated (new-space))
!(psr-load-environment &psr-env-mutated)

(= (psr-manifest-entry-present $space $bytes)
   (let $atom (parse $bytes)
     (if (== (repr $atom) $bytes)
       (_minimal-space-contains-exact $space $atom)
       False)))

(= (psr-manifest-present $space LNil) True)
(= (psr-manifest-present $space (LCons $bytes $rest))
   (if (psr-manifest-entry-present $space $bytes)
     (psr-manifest-present $space $rest)
     False))

(= (psr-space-snapshot $space $manifest)
   (if (gic-no-duplicates $manifest)
     (if (== (space-len $space) (gic-list-length $manifest))
       (if (psr-manifest-present $space $manifest)
         (let $revision (_minimal-space-revision $space)
           (let $material
             (SpaceSnapshotMaterialV1
               "exact-ground-space-v1" $manifest $revision)
             (SpaceSnapshotV1
               $material (sha256 (repr $material)))))
         (SpaceSnapshotRejectedV1 ManifestMismatchV1))
       (SpaceSnapshotRejectedV1 CardinalityMismatchV1))
     (SpaceSnapshotRejectedV1 DuplicateManifestEntryV1)))

; ---------- Runtime and checker identities ---------------------------------
(= (psr-runtime-prime-identity $space)
   (case (prime-package $space)
     (((PrimeDefV1
          $identity $language $contexts $typing $results $effects $evidence)
        $identity)
      ($_ (PrimeIdentityRejectedV1 InvalidRuntimePackageV1)))))

(= (psr-eval-package)
   (pmcp-package-v1 (pmh-eval-rules) LNil))

(= (psr-cache-for-package $package)
   (case (pmcp-project-package $package)
     (((PMCPProjected $presentation) $presentation)
      ($_ (PMCPProjectionRejected InvalidSubjectPackageV1)))))

(= (psr-eval-cache)
   (psr-cache-for-package (psr-eval-package)))

(= (psr-package-admission)
   (ppi-admit (psr-eval-package) (psr-eval-cache)))

(= (psr-admission-identity
      (PrimePackageAdmissionV1 $identity $handle $package $cache))
   $identity)

(= (psr-package-identity)
   (psr-admission-identity (psr-package-admission)))

; ---------- Canonical SubjectRefV1 -----------------------------------------
(= (psr-conversion-policy)
   (ConversionPolicyV1
     "prime-rooted-conversion-v1"
     OrdinaryUserRulesExcludedFromDefinitionalEquality
     UnboundedByDefault))

(= (psr-effect-policy)
   (EffectPolicyV1
     OrdinaryRuntimeEffects SnapshotBoundCheckingEnvironment))

(= (psr-subject-material-with-identity
      $space $package-identity $program-syntax $runtime-judgment
      $checked-judgment $prime-identity)
   (let $manifest (psr-environment-manifest)
     (let $snapshot (psr-space-snapshot $space $manifest)
       (SubjectMaterialV1
         "subject-ref-v1"
         $package-identity
         $prime-identity
         (QuotedProgramV1 $program-syntax)
         (EnvironmentBindingV1 $manifest $snapshot)
         (QuotedPrimeJudgmentV1 $runtime-judgment)
         (CheckedJudgmentV1 $checked-judgment)
         (psr-conversion-policy)
         (psr-effect-policy)))))

(= (psr-make-subject-ref $material)
   (let $digest (sha256 (repr $material))
     (SubjectRefV1
       $material $digest (SubjectLocalHandleV1 $digest))))

(= (psr-build-subject-with-identity
      $space $package-identity $program-syntax $runtime-judgment
      $checked-judgment $prime-identity)
   (psr-make-subject-ref
     (psr-subject-material-with-identity
       $space $package-identity $program-syntax $runtime-judgment
       $checked-judgment $prime-identity)))

(= (psr-build-subject
      $space $package-identity $program-syntax $runtime-judgment
      $checked-judgment)
   (psr-build-subject-with-identity
     $space $package-identity $program-syntax $runtime-judgment
     $checked-judgment (psr-runtime-prime-identity $space)))

(= (psr-pick-subject $space)
   (psr-build-subject
     $space
     (psr-package-identity)
     (quote (pmh-choose))
     (quote (May (PrimeEvaluate (pmh-choose)) Nat))
     (pmh-eval-goal-complete-choose)))

(= (psr-only-subject $space)
   (psr-build-subject
     $space
     (psr-package-identity)
     (quote (pmh-only))
     (quote (Must (PrimeEvaluate (pmh-only)) Nat))
     (pmh-eval-goal-complete-only)))

(= (psr-subject-checked-judgment
      (SubjectRefV1
        (SubjectMaterialV1
          "subject-ref-v1" $package-identity $prime-identity
          (QuotedProgramV1 $program-syntax)
          (EnvironmentBindingV1 $manifest
            (SpaceSnapshotV1
              (SpaceSnapshotMaterialV1
                "exact-ground-space-v1" $manifest $revision)
              $snapshot-digest))
          (QuotedPrimeJudgmentV1 $runtime-judgment)
          (CheckedJudgmentV1 $checked-judgment)
          $conversion-policy $effect-policy)
        $digest $handle))
   $checked-judgment)

(= (psr-subject-space-revision
      (SubjectRefV1
        (SubjectMaterialV1
          "subject-ref-v1" $package-identity $prime-identity
          (QuotedProgramV1 $program-syntax)
          (EnvironmentBindingV1 $manifest
            (SpaceSnapshotV1
              (SpaceSnapshotMaterialV1 $format $manifest $revision)
              $snapshot-digest))
          (QuotedPrimeJudgmentV1 $runtime-judgment)
          (CheckedJudgmentV1 $checked-judgment)
          $conversion-policy $effect-policy)
        $digest $handle))
   $revision)

(= (psr-subject-valid $space $expected-package-identity
      (SubjectRefV1
        (SubjectMaterialV1
          "subject-ref-v1" $package-identity $prime-identity
          (QuotedProgramV1 $program-syntax)
          (EnvironmentBindingV1 $manifest
            (SpaceSnapshotV1
              (SpaceSnapshotMaterialV1
                "exact-ground-space-v1" $manifest $revision)
              $snapshot-digest))
          (QuotedPrimeJudgmentV1 $runtime-judgment)
          (CheckedJudgmentV1 $checked-judgment)
          (ConversionPolicyV1
            "prime-rooted-conversion-v1"
            OrdinaryUserRulesExcludedFromDefinitionalEquality
            UnboundedByDefault)
          (EffectPolicyV1
            OrdinaryRuntimeEffects SnapshotBoundCheckingEnvironment))
        $digest (SubjectLocalHandleV1 $handle)))
   (let $material
     (SubjectMaterialV1
       "subject-ref-v1" $package-identity $prime-identity
       (QuotedProgramV1 $program-syntax)
       (EnvironmentBindingV1 $manifest
         (SpaceSnapshotV1
           (SpaceSnapshotMaterialV1
             "exact-ground-space-v1" $manifest $revision)
           $snapshot-digest))
       (QuotedPrimeJudgmentV1 $runtime-judgment)
       (CheckedJudgmentV1 $checked-judgment)
       (ConversionPolicyV1
         "prime-rooted-conversion-v1"
         OrdinaryUserRulesExcludedFromDefinitionalEquality
         UnboundedByDefault)
       (EffectPolicyV1
         OrdinaryRuntimeEffects SnapshotBoundCheckingEnvironment))
     (if (== $package-identity $expected-package-identity)
       (if (== $prime-identity (psr-runtime-prime-identity $space))
         (if (==
               (SpaceSnapshotV1
                 (SpaceSnapshotMaterialV1
                   "exact-ground-space-v1" $manifest $revision)
                 $snapshot-digest)
               (psr-space-snapshot $space $manifest))
           (if (== $digest (sha256 (repr $material)))
             (== $handle $digest)
             False)
           False)
         False)
       False)))
; ---------- Structurally indexed generic checking --------------------------
(= (psr-check $admission $space $subject $goal $derivation)
   (case $admission
     (((PrimePackageAdmissionV1
          $package-identity $handle $package $cache)
        (if (psr-subject-valid $space $package-identity $subject)
          (if (== (psr-subject-checked-judgment $subject) $goal)
            (if (ppi-check-admitted
                  $admission $package $goal $derivation)
              (Checked
                $package-identity $subject $goal $derivation)
              False)
            False)
          False))
      ($_ False))))

(= (psr-replay $admission $space
      (Checked $package-identity $subject $goal $derivation))
   (==
     (psr-check $admission $space $subject $goal $derivation)
     (Checked $package-identity $subject $goal $derivation)))
; ---------- Runtime occurrences and untrusted observation production -------
!(bind! &psr-occurrence-counter (new-state 0))

(= (psr-next-occurrence)
   (let $current (get-state &psr-occurrence-counter)
     (let $_updated
       (change-state! &psr-occurrence-counter (+ $current 1))
       (OccurrenceIdV1 $current))))

; The producer is deliberately specialized to this calibration program.  It
; discards the runtime judgment field after invoking the exact indexed query;
; replay trusts only SubjectRefV1 plus the checked operational derivation.
(= (psr-normalize-pick-observation $subject $occurrence
      (PrimeVerdict Established $runtime-judgment
        (MayWitness $index Z Nat $edge)))
   (RuntimeObservationV1
     $subject $occurrence (MayWitnessV1 $index Z Nat $edge)))

(= (psr-produce-pick-certificate $space)
   (let $subject (psr-pick-subject $space)
     (let $checked
       (psr-check
         (psr-package-admission) $space $subject
         (pmh-eval-goal-complete-choose)
         (pmh-eval-proof-complete-choose))
       (let $occurrence (psr-next-occurrence)
         (let $verdict
           (prime-judge $space
             (May (PrimeEvaluate (pmh-choose)) Nat))
           (let $observation
             (psr-normalize-pick-observation
               $subject $occurrence (noeval $verdict))
             (PrimeProgramCertificateV1
               $occurrence $checked $observation)))))))

(= (psr-certificate-occurrence
      (PrimeProgramCertificateV1 $occurrence $checked $observation))
   $occurrence)

(= (psr-program-certificate-valid-at
      $admission $space $expected-occurrence
      (PrimeProgramCertificateV1
        $occurrence
        (Checked $package-identity $subject $goal $derivation)
        (RuntimeObservationV1
          $subject $occurrence
          (MayWitnessV1 $index Z Nat $edge))))
   (if (== $expected-occurrence $occurrence)
     (if (psr-replay
           $admission $space
           (Checked $package-identity $subject $goal $derivation))
       (pmh-choose-bag-agrees
         (collapse (evalc (pmh-choose) $space)))
       False)
     False))
; ---------- Subject and package mutations ----------------------------------
(= (psr-zero-digest)
   "0000000000000000000000000000000000000000000000000000000000000000")

(= (psr-forged-digest-subject
      (SubjectRefV1 $material $digest $handle))
   (SubjectRefV1
     $material (psr-zero-digest) (SubjectLocalHandleV1 (psr-zero-digest))))

(= (psr-forged-handle-subject
      (SubjectRefV1 $material $digest $handle))
   (SubjectRefV1
     $material $digest (SubjectLocalHandleV1 (psr-zero-digest))))

(= (psr-fake-prime-identity)
   (PrimeIdentityV1
     (Language he)
     (LongName metta-he)
     (SchemaVersion 1)
     (DialectVersion 0 2)))

(= (psr-different-dialect-subject $space)
   (psr-build-subject-with-identity
     $space
     (psr-package-identity)
     (quote (pmh-choose))
     (quote (May (PrimeEvaluate (pmh-choose)) Nat))
     (pmh-eval-goal-complete-choose)
     (psr-fake-prime-identity)))

(= (psr-different-package-subject $space)
   (psr-build-subject
     $space
     (ppi-package-identity (ppi-swapped-package))
     (quote (pmh-choose))
     (quote (May (PrimeEvaluate (pmh-choose)) Nat))
     (pmh-eval-goal-complete-choose)))

(= (psr-wrong-package-admission)
   (ppi-admit
     (ppi-swapped-package)
     (psr-cache-for-package (ppi-swapped-package))))

; ---------- Positive and falsifying gates ----------------------------------
!(assertEqual
   (pmcp-cache-valid (psr-eval-package) (psr-eval-cache)) True)
!(assertEqual
   (psr-subject-valid
     &psr-env (psr-package-identity) (psr-pick-subject &psr-env))
   True)
!(assertEqual
   (psr-subject-valid
     &psr-env (psr-package-identity) (psr-only-subject &psr-env))
   True)

!(bind! &psr-checked-pick
   (psr-check
     (psr-package-admission) &psr-env (psr-pick-subject &psr-env)
     (pmh-eval-goal-complete-choose)
     (pmh-eval-proof-complete-choose)))
!(assertEqual
   (psr-replay (psr-package-admission) &psr-env &psr-checked-pick)
   True)

!(bind! &psr-certificate-a (psr-produce-pick-certificate &psr-env))
!(bind! &psr-certificate-b (psr-produce-pick-certificate &psr-env))
!(bind! &psr-occurrence-a (psr-certificate-occurrence &psr-certificate-a))
!(bind! &psr-occurrence-b (psr-certificate-occurrence &psr-certificate-b))
!(assertEqual
   (psr-program-certificate-valid-at
     (psr-package-admission) &psr-env
     &psr-occurrence-a &psr-certificate-a)
   True)
!(assertEqual
   (psr-program-certificate-valid-at
     (psr-package-admission) &psr-env
     &psr-occurrence-b &psr-certificate-b)
   True)
!(assertEqual (== &psr-occurrence-a &psr-occurrence-b) False)

; Same derivation, but a different authenticated program subject.
!(assertEqual
   (psr-replay
     (psr-package-admission) &psr-env
     (Checked
       (psr-package-identity)
       (psr-only-subject &psr-env)
       (pmh-eval-goal-complete-choose)
       (pmh-eval-proof-complete-choose)))
   False)

; The old quotation oracle remains only as a regression negative.
!(assertEqual
   (pmh-certify-choose-may
     (noeval (PrimeVerdict Established
       (May (PrimeEvaluate (pmh-only)) Nat)
       (MayWitness 0 Z Nat exact))))
   False)

; A temporal space mutation invalidates the prior subject even after content
; is restored, because its revision has changed.
!(bind! &psr-mutated-subject (psr-pick-subject &psr-env-mutated))
!(assertEqual (psr-subject-space-revision &psr-mutated-subject) 7)
!(assertEqual (_minimal-space-revision &psr-env-mutated) 7)
!(bind! &psr-mutated-checked
   (psr-check
     (psr-package-admission) &psr-env-mutated &psr-mutated-subject
     (pmh-eval-goal-complete-choose)
     (pmh-eval-proof-complete-choose)))
!(assertEqual
   (psr-replay
     (psr-package-admission) &psr-env-mutated &psr-mutated-checked)
   True)
!(add-atom &psr-env-mutated PSRMutation)
!(assertEqual (_minimal-space-revision &psr-env-mutated) 8)
!(assertEqual
   (psr-replay
     (psr-package-admission) &psr-env-mutated &psr-mutated-checked)
   False)
!(remove-atom &psr-env-mutated PSRMutation)
!(assertEqual (_minimal-space-revision &psr-env-mutated) 9)
!(assertEqual (psr-subject-space-revision &psr-mutated-subject) 7)
!(assertEqual
   (psr-replay
     (psr-package-admission) &psr-env-mutated &psr-mutated-checked)
   False)

!(assertEqual
   (psr-subject-valid
     &psr-env (psr-package-identity)
     (psr-different-dialect-subject &psr-env))
   False)
!(assertEqual
   (psr-subject-valid
     &psr-env (psr-package-identity)
     (psr-different-package-subject &psr-env))
   False)
!(assertEqual
   (psr-program-certificate-valid-at
     (psr-package-admission) &psr-env
     &psr-occurrence-b &psr-certificate-a)
   False)
!(assertEqual
   (psr-subject-valid
     &psr-env (psr-package-identity)
     (psr-forged-digest-subject (psr-pick-subject &psr-env)))
   False)
!(assertEqual
   (psr-subject-valid
     &psr-env (psr-package-identity)
     (psr-forged-handle-subject (psr-pick-subject &psr-env)))
   False)
!(assertEqual
   (psr-replay
     (psr-wrong-package-admission) &psr-env &psr-checked-pick)
   False)

!(println! (PrimeSubjectRefV1Summary 23 23 0))
