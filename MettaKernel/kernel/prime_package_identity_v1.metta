; =============================================================================
; prime_package_identity_v1.metta
;
; Phase-1 calibration for authenticated Prime checking packages.  The sole
; package authority is PrimeRulePackageV1 from the minimal checker fixture.
; Canonical bytes are the strict parseable representation of that exact ground
; value; the digest is computed by CeTTa rather than supplied by the author.
; =============================================================================

!(import! &self prime_minimal_checking_package_v0)

; ---------- One package with a conversion judgment --------------------------
(= (ppi-A) (PApp "ppi.A" LNil))
(= (ppi-B) (PApp "ppi.B" LNil))
(= (ppi-Imp $left $right) (PApp "ppi.Imp" (pmcp-l2 $left $right)))
(= (ppi-Proves $formula) (PApp "ppi.Proves" (pmcp-l1 $formula)))
(= (ppi-Convertible $left $right)
   (PApp "ppi.Convertible" (pmcp-l2 $left $right)))

(= (ppi-rule-a)
   (GRule "ppi.ax-a" LNil LNil (ppi-Proves (ppi-A))))
(= (ppi-rule-imp)
   (GRule "ppi.ax-imp" LNil LNil
     (ppi-Proves (ppi-Imp (ppi-A) (ppi-B)))))
(= (ppi-rule-mp)
   (GRule "ppi.mp"
     (pmcp-l2 (Formal "antecedent" 0) (Formal "consequent" 0))
     (pmcp-l2
       (ppi-Proves (FVar "antecedent"))
       (ppi-Proves (ppi-Imp (FVar "antecedent") (FVar "consequent"))))
     (ppi-Proves (FVar "consequent"))))
(= (ppi-conversion-refl)
   (GRule "ppi.conv-refl" (pmcp-l1 (Formal "term" 0)) LNil
     (ppi-Convertible (FVar "term") (FVar "term"))))

(= (ppi-rules) (pmcp-l3 (ppi-rule-a) (ppi-rule-imp) (ppi-rule-mp)))
(= (ppi-conversions) (pmcp-l1 (ppi-conversion-refl)))
(= (ppi-package) (pmcp-package-v1 (ppi-rules) (ppi-conversions)))

; The structural companion is independently stated.  The rule payload remains
; the exact ordered append that the checker consumes.
(= (ppi-cache)
   (GPresentation
     (pmcp-l3
       (CDecl "ppi.A" 0)
       (CDecl "ppi.Imp" 2)
       (CDecl "ppi.B" 0))
     (pmcp-l2
       (JDecl "ppi.Proves" 1)
       (JDecl "ppi.Convertible" 2))
     (gic-append (ppi-rules) (ppi-conversions))))

(= (ppi-proof-a) (GProof (GRuleInst "ppi.ax-a" LNil) PrNil))
(= (ppi-proof-imp) (GProof (GRuleInst "ppi.ax-imp" LNil) PrNil))
(= (ppi-proof-b)
   (GProof
     (GRuleInst "ppi.mp" (pmcp-l2 (ppi-A) (ppi-B)))
     (pmcp-pr2 (ppi-proof-a) (ppi-proof-imp))))
(= (ppi-goal-b) (ppi-Proves (ppi-B)))

; ---------- Canonical identity and fail-closed admission --------------------
(= (ppi-canonical-bytes $package) (repr $package))

(= (ppi-package-identity $package)
   (case $package
     (((PrimeRulePackageV1
          "prime-rule-package-v1" "prime" "0.5" $rules $conversions)
        (PackageIdentityV1
          "prime-rule-package-v1" "prime" "0.5"
          (sha256 (repr $package))))
      ($_ (PackageIdentityRejectedV1 InvalidPackageMetadataV1)))))

(= (ppi-admit $package $cached)
   (case (ppi-package-identity $package)
     (((PackageIdentityV1 $format $dialect $version $digest)
        (if (pmcp-cache-valid $package $cached)
          (PrimePackageAdmissionV1
            (PackageIdentityV1 $format $dialect $version $digest)
            $digest $package $cached)
          (PrimePackageAdmissionRejectedV1 CacheMismatchV1)))
      ($_ (PrimePackageAdmissionRejectedV1 InvalidPackageV1)))))

; Authored identity claims are never authority: the computed identity must
; agree exactly before the ordinary admission path is exposed.
(= (ppi-admit-claimed $package $cached $claimed)
   (case (ppi-package-identity $package)
     (($computed
        (if (== $computed $claimed)
          (ppi-admit $package $cached)
          (PrimePackageAdmissionRejectedV1 ClaimedDigestMismatchV1))))))

; A serialized package is admissible only in its one canonical spelling.
(= (ppi-admit-bytes $bytes $cached)
   (case (parse $bytes)
     (((Error $term $reason)
        (PrimePackageAdmissionRejectedV1 MalformedSerializationV1))
      ($parsed
        (if (== (repr $parsed) $bytes)
          (ppi-admit $parsed $cached)
          (PrimePackageAdmissionRejectedV1 NonCanonicalSerializationV1))))))

; Replay is indexed by both the stored package and its recomputed identity.
; A token cannot be carried across any package mutation.
(= (ppi-check-admitted $admission $package $goal $proof)
   (case $admission
     (((PrimePackageAdmissionV1 $identity $handle $stored $cached)
        (case (ppi-package-identity $package)
          (($computed
            (if (== $stored $package)
              (if (== $identity $computed)
                (gic-check $cached $goal $proof)
                False)
              False)))))
      ($_ False))))

; ---------- Mutation fixtures ------------------------------------------------
(= (ppi-premise-mutated-rules)
   (pmcp-l3
     (ppi-rule-a)
     (ppi-rule-imp)
     (GRule "ppi.mp"
       (pmcp-l2 (Formal "antecedent" 0) (Formal "consequent" 0))
       (pmcp-l2
         (ppi-Proves (ppi-B))
         (ppi-Proves (ppi-Imp (FVar "antecedent") (FVar "consequent"))))
       (ppi-Proves (FVar "consequent")))))
(= (ppi-premise-mutated-package)
   (pmcp-package-v1 (ppi-premise-mutated-rules) (ppi-conversions)))

(= (ppi-swapped-package)
   (pmcp-package-v1
     (pmcp-l3 (ppi-rule-imp) (ppi-rule-a) (ppi-rule-mp))
     (ppi-conversions)))

(= (ppi-conversion-mutated-package)
   (pmcp-package-v1
     (ppi-rules)
     (pmcp-l1
       (GRule "ppi.conv-refl" (pmcp-l1 (Formal "term" 0)) LNil
         (ppi-Convertible (FVar "term") (ppi-A))))))

(= (ppi-zero-digest)
   "0000000000000000000000000000000000000000000000000000000000000000")
(= (ppi-false-identity)
   (PackageIdentityV1
     "prime-rule-package-v1" "prime" "0.5" (ppi-zero-digest)))

; ---------- Positive and falsifying gates -----------------------------------
!(assertEqual (pmcp-package-valid (ppi-package)) True)
!(assertEqual (pmcp-cache-valid (ppi-package) (ppi-cache)) True)
!(assertEqual
   (ppi-check-admitted
     (ppi-admit (ppi-package) (ppi-cache))
     (ppi-package) (ppi-goal-b) (ppi-proof-b))
   True)
!(assertEqual
   (ppi-admit-bytes (ppi-canonical-bytes (ppi-package)) (ppi-cache))
   (ppi-admit (ppi-package) (ppi-cache)))

!(assertEqual
   (== (ppi-package-identity (ppi-package))
       (ppi-package-identity (ppi-premise-mutated-package)))
   False)
!(assertEqual
   (== (ppi-package-identity (ppi-package))
       (ppi-package-identity (ppi-swapped-package)))
   False)
!(assertEqual
   (== (ppi-package-identity (ppi-package))
       (ppi-package-identity (ppi-conversion-mutated-package)))
   False)
!(assertEqual
   (ppi-admit-bytes
     (str:concat " " (ppi-canonical-bytes (ppi-package))) (ppi-cache))
   (PrimePackageAdmissionRejectedV1 NonCanonicalSerializationV1))
!(assertEqual
   (ppi-admit-claimed (ppi-package) (ppi-cache) (ppi-false-identity))
   (PrimePackageAdmissionRejectedV1 ClaimedDigestMismatchV1))
!(assertEqual
   (ppi-admit (ppi-package) (pmcp-mp-cache))
   (PrimePackageAdmissionRejectedV1 CacheMismatchV1))
!(assertEqual
   (ppi-check-admitted
     (ppi-admit (ppi-package) (ppi-cache))
     (ppi-premise-mutated-package) (ppi-goal-b) (ppi-proof-b))
   False)
!(assertEqual
   (ppi-check-admitted
     (ppi-admit (ppi-package) (ppi-cache))
     (ppi-swapped-package) (ppi-goal-b) (ppi-proof-b))
   False)
!(assertEqual
   (ppi-check-admitted
     (ppi-admit (ppi-package) (ppi-cache))
     (ppi-conversion-mutated-package) (ppi-goal-b) (ppi-proof-b))
   False)
!(assertEqual
   (ppi-admit-bytes "(PrimeRulePackageV1" (ppi-cache))
   (PrimePackageAdmissionRejectedV1 MalformedSerializationV1))

!(println! "PRIME_PACKAGE_CANONICAL_BEGIN")
!(println! (ppi-canonical-bytes (ppi-package)))
!(println! "PRIME_PACKAGE_CANONICAL_END")
!(println! "PRIME_PACKAGE_DIGEST_BEGIN")
!(case (ppi-package-identity (ppi-package))
   (((PackageIdentityV1 $format $dialect $version $digest)
      (println! $digest))))
!(println! "PRIME_PACKAGE_DIGEST_END")
!(println! (PrimePackageIdentitySummaryV1 14 14 0))
