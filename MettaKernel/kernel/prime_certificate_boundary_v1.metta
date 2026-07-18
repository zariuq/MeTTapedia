; =============================================================================
; prime_certificate_boundary_v1.metta
;
; Cross-runtime certificate-boundary calibration for the source-derived Prime
; fragment.  A certificate commits to the compiled package, the exact source
; snapshot, dialect, inert program pattern, checked judgment, and raw proof.
; Validation replays the unchanged generic checker; hashes and handles only
; bind identity and never grant derivability.
; =============================================================================

!(import! &self prime_fragment_adequacy_v1)

; ---------- Canonical source and subject identity --------------------------
(= (pcb-source-bytes $source)
   (case $source
     (($resolved (repr $resolved)))))
(= (pcb-source-digest $source) (sha256 (pcb-source-bytes $source)))

(= (pcb-source-snapshot $source)
   (PrimeFragmentSourceSnapshotV1
     "prime-fragment-source-v1" (pcb-source-digest $source)))

(= (pcb-subject-material $source $program $goal)
   (PrimeFragmentSubjectMaterialV1
     "prime-fragment-subject-v1"
     (ppi-package-identity (pfa-package-from $source))
     (pcb-source-snapshot $source)
     "prime"
     $program
     $goal))

(= (pcb-make-subject $source $program $goal)
   (let $material (pcb-subject-material $source $program $goal)
     (let $digest (sha256 (repr $material))
       (PrimeFragmentSubjectRefV1
         $material $digest (SubjectLocalHandleV1 $digest)))))

(= (pcb-program-goal-agree $program $goal)
   (case (PCBProgramGoalPairV1 $program $goal)
     (((PCBProgramGoalPairV1
          (PApp "wex.add" $arguments)
          (PApp "wex1.Evals"
            (LCons (PApp "wex.add" $arguments)
              (LCons $result LNil))))
        True)
      ((PCBProgramGoalPairV1
          (PApp "wex.length" (LCons $input LNil))
          (PApp "wex2.LenIs" (LCons $input (LCons $result LNil))))
        True)
      ((PCBProgramGoalPairV1
          (PApp "wex.pick" LNil)
          (PApp "wex3.MayEval"
            (LCons (PApp "wex.pick" LNil) (LCons $result LNil))))
        True)
      ($_ False))))

(= (pcb-subject-goal
      (PrimeFragmentSubjectRefV1
        (PrimeFragmentSubjectMaterialV1
          $format $package-identity $source-snapshot $dialect
          $program $goal)
        $digest $handle))
   $goal)

(= (pcb-subject-valid $source $subject)
   (case $subject
     (((PrimeFragmentSubjectRefV1
          (PrimeFragmentSubjectMaterialV1
            "prime-fragment-subject-v1"
            $package-identity
            (PrimeFragmentSourceSnapshotV1
              "prime-fragment-source-v1" $source-digest)
            "prime"
            $program
            $goal)
          $digest
          (SubjectLocalHandleV1 $handle))
        (let $material
          (PrimeFragmentSubjectMaterialV1
            "prime-fragment-subject-v1"
            $package-identity
            (PrimeFragmentSourceSnapshotV1
              "prime-fragment-source-v1" $source-digest)
            "prime"
            $program
            $goal)
          (if (== $package-identity
                  (ppi-package-identity (pfa-package-from $source)))
            (if (== $source-digest (pcb-source-digest $source))
              (if (pcb-program-goal-agree $program $goal)
                (if (== $digest (sha256 (repr $material)))
                  (== $handle $digest)
                  False)
                False)
              False)
            False)))
      ($_ False))))

; ---------- Certificate material and validation ----------------------------
(= (pcb-certificate-material $subject $goal $proof)
   (PrimeFragmentCertificateMaterialV1
     "prime-fragment-certificate-v1" $subject $goal $proof))

(= (pcb-make-certificate $source $program $goal $proof)
   (let $subject (pcb-make-subject $source $program $goal)
     (let $material (pcb-certificate-material $subject $goal $proof)
       (PrimeFragmentCertificateV1
         $material (sha256 (repr $material))))))

(= (pcb-certificate-valid $source $certificate)
   (case $certificate
     (((PrimeFragmentCertificateV1
          (PrimeFragmentCertificateMaterialV1
            "prime-fragment-certificate-v1" $subject $goal $proof)
          $digest)
        (let $material (pcb-certificate-material $subject $goal $proof)
          (if (== $digest (sha256 (repr $material)))
            (if (pcb-subject-valid $source $subject)
              (if (== (pcb-subject-goal $subject) $goal)
                (pmcp-check-reference
                  (pfa-package-from $source) $goal $proof)
                False)
              False)
            False)))
      ($_ False))))

(= (pcb-certificate-bytes $certificate)
   (case $certificate
     (($resolved (repr $resolved)))))

; ---------- Canonical certificate and isolated mutations -------------------
(= (pcb-zero-digest)
   "0000000000000000000000000000000000000000000000000000000000000000")

(= (pcb-canonical-program)
   (wex1-add-t (wex1-two) (wex1-one)))

(= (pcb-canonical-certificate)
   (pcb-make-certificate
     (pfa-canonical-source)
     (pcb-canonical-program)
     (wex1-goal)
     (wex1-proof-2)))

(= (pcb-wrong-program-certificate)
   (pcb-make-certificate
     (pfa-canonical-source)
     (wex1-add-t (wex1-one) (wex1-one))
     (wex1-goal)
     (wex1-proof-2)))

(= (pcb-wrong-goal-certificate)
   (pcb-make-certificate
     (pfa-canonical-source)
     (pcb-canonical-program)
     (wex1-wrong-goal)
     (wex1-proof-2)))

(= (pcb-skipped-proof-certificate)
   (pcb-make-certificate
     (pfa-canonical-source)
     (pcb-canonical-program)
     (wex1-goal)
     (wex1-skipped-proof)))

(= (pcb-forge-subject-digest
      (PrimeFragmentSubjectRefV1 $material $digest $handle))
   (PrimeFragmentSubjectRefV1
     $material (pcb-zero-digest) (SubjectLocalHandleV1 (pcb-zero-digest))))

(= (pcb-replace-subject
      (PrimeFragmentCertificateV1
        (PrimeFragmentCertificateMaterialV1
          "prime-fragment-certificate-v1" $old-subject $goal $proof)
        $old-digest)
      $new-subject)
   (let $material (pcb-certificate-material $new-subject $goal $proof)
     (PrimeFragmentCertificateV1
       $material (sha256 (repr $material)))))

(= (pcb-forged-subject-certificate)
   (case (pcb-canonical-certificate)
     (((PrimeFragmentCertificateV1
          (PrimeFragmentCertificateMaterialV1
            "prime-fragment-certificate-v1" $subject $goal $proof)
          $digest)
        (pcb-replace-subject
          (pcb-canonical-certificate)
          (pcb-forge-subject-digest $subject))))))

(= (pcb-forged-certificate-digest)
   (case (pcb-canonical-certificate)
     (((PrimeFragmentCertificateV1 $material $digest)
        (PrimeFragmentCertificateV1 $material (pcb-zero-digest))))))

; ---------- Positive and falsifying gates ----------------------------------
!(assertEqual
   (pcb-certificate-valid
     (pfa-canonical-source) (pcb-canonical-certificate))
   True)
!(assertEqual
   (pcb-certificate-valid
     (pfa-canonical-source) (pcb-wrong-program-certificate))
   False)
!(assertEqual
   (pcb-certificate-valid
     (pfa-canonical-source) (pcb-wrong-goal-certificate))
   False)
!(assertEqual
   (pcb-certificate-valid
     (pfa-canonical-source) (pcb-skipped-proof-certificate))
   False)
!(assertEqual
   (pcb-certificate-valid
     (pfa-add-deleted-source) (pcb-canonical-certificate))
   False)
!(assertEqual
   (pcb-certificate-valid
     (pfa-canonical-source) (pcb-forged-subject-certificate))
   False)
!(assertEqual
   (pcb-certificate-valid
     (pfa-canonical-source) (pcb-forged-certificate-digest))
   False)
!(assertEqual
   (== (pcb-certificate-bytes (pcb-canonical-certificate))
       (pcb-certificate-bytes (pcb-wrong-program-certificate)))
   False)

!(println! "PRIME_CERTIFICATE_CANONICAL_BEGIN")
!(println! (pcb-certificate-bytes (pcb-canonical-certificate)))
!(println! "PRIME_CERTIFICATE_CANONICAL_END")
!(println! "PRIME_CERTIFICATE_DIGEST_BEGIN")
!(case (pcb-canonical-certificate)
   (((PrimeFragmentCertificateV1 $material $digest)
      (println! $digest))))
!(println! "PRIME_CERTIFICATE_DIGEST_END")
!(println! (PrimeCertificateBoundaryMeTTaSummaryV1 8 8 0))
