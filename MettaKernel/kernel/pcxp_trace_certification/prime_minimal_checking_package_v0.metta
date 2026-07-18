; =============================================================================
; prime_minimal_checking_package_v0.metta
;
; Calibration fixture for a syntax-free checking package.
;
; The authored source is only an ordered list of generic inference rules.
; Constructor and judgment declarations required by the current generic checker
; are deterministically projected from fixed occurrences in those rules.  A
; cached presentation is usable only when it is exactly the projected value.
;
; This fixture claims package-relative certificate replay only.  It does not
; claim consistency, source adequacy, truth, parsing, or gluing.
; =============================================================================

!(import! &self generic_inference_checker_v0)

; ---------- Stable finite-list constructors ---------------------------------
(= (pmcp-l1 $a) (LCons $a LNil))
(= (pmcp-l2 $a $b) (LCons $a (LCons $b LNil)))
(= (pmcp-l3 $a $b $c) (LCons $a (LCons $b (LCons $c LNil))))
(= (pmcp-l4 $a $b $c $d)
   (LCons $a (LCons $b (LCons $c (LCons $d LNil)))))
(= (pmcp-pr2 $a $b) (PrCons $a (PrCons $b PrNil)))

; ---------- Declaration projection ------------------------------------------
; Lookup results distinguish absence from an arity conflict.
(= (pmcp-find-constructor LNil $head) PMCPAbsent)
(= (pmcp-find-constructor (LCons (CDecl $candidate $arity) $rest) $head)
   (if (== $candidate $head)
     (PMCPFound $arity)
     (pmcp-find-constructor $rest $head)))

(= (pmcp-find-judgment LNil $head) PMCPAbsent)
(= (pmcp-find-judgment (LCons (JDecl $candidate $arity) $rest) $head)
   (if (== $candidate $head)
     (PMCPFound $arity)
     (pmcp-find-judgment $rest $head)))

(= (pmcp-add-constructor $constructors $head $arity)
   (case (pmcp-find-constructor $constructors $head)
     ((PMCPAbsent
        (PMCPConstructorsOK
          (gic-append $constructors (pmcp-l1 (CDecl $head $arity)))))
      ((PMCPFound $prior)
        (if (== $prior $arity)
          (PMCPConstructorsOK $constructors)
          (PMCPProjectionRejected ConstructorArityConflictV0)))
      ($_ (PMCPProjectionRejected MalformedConstructorTableV0)))))

(= (pmcp-add-judgment $judgments $head $arity)
   (case (pmcp-find-judgment $judgments $head)
     ((PMCPAbsent
        (PMCPJudgmentsOK
          (gic-append $judgments (pmcp-l1 (JDecl $head $arity)))))
      ((PMCPFound $prior)
        (if (== $prior $arity)
          (PMCPJudgmentsOK $judgments)
          (PMCPProjectionRejected JudgmentArityConflictV0)))
      ($_ (PMCPProjectionRejected MalformedJudgmentTableV0)))))

; Fixed nested applications are structural constructors.  Free variables and
; de Bruijn variables are holes/variables, while binders and substitutions are
; generic Pattern structure and require no declaration.
(= (pmcp-collect-fixed-list $constructors LNil)
   (PMCPConstructorsOK $constructors))
(= (pmcp-collect-fixed-list $constructors (LCons $pattern $rest))
   (case (pmcp-collect-fixed $constructors $pattern)
     (((PMCPConstructorsOK $next)
        (pmcp-collect-fixed-list $next $rest))
      ((PMCPProjectionRejected $reason)
        (PMCPProjectionRejected $reason)))))

(= (pmcp-collect-fixed $constructors $pattern)
   (case $pattern
     (((Var $index) (PMCPConstructorsOK $constructors))
      ((FVar $name) (PMCPConstructorsOK $constructors))
      ((PApp $head $arguments)
        (case (pmcp-add-constructor
                $constructors $head (gic-list-length $arguments))
          (((PMCPConstructorsOK $next)
            (pmcp-collect-fixed-list $next $arguments))
           ((PMCPProjectionRejected $reason)
             (PMCPProjectionRejected $reason)))))
      ((PLam $binder $body) (pmcp-collect-fixed $constructors $body))
      ((PMultiLam $arity $binders $body)
        (pmcp-collect-fixed $constructors $body))
      ((PSubst $body $replacement)
        (case (pmcp-collect-fixed $constructors $body)
          (((PMCPConstructorsOK $next)
            (pmcp-collect-fixed $next $replacement))
           ((PMCPProjectionRejected $reason)
             (PMCPProjectionRejected $reason)))))
      ((PCollection $kind $elements $rest)
        (pmcp-collect-fixed-list $constructors $elements))
      ($_ (PMCPProjectionRejected MalformedPatternV0)))))

; The outer application is a judgment form; only its arguments contribute
; fixed data constructors.
(= (pmcp-collect-judgment $constructors $judgments $pattern)
   (case $pattern
     (((PApp $head $arguments)
        (case (pmcp-add-judgment
                $judgments $head (gic-list-length $arguments))
          (((PMCPJudgmentsOK $next-judgments)
            (case (pmcp-collect-fixed-list $constructors $arguments)
              (((PMCPConstructorsOK $next-constructors)
                (PMCPDeclsOK $next-constructors $next-judgments))
               ((PMCPProjectionRejected $reason)
                 (PMCPProjectionRejected $reason)))))
           ((PMCPProjectionRejected $reason)
             (PMCPProjectionRejected $reason)))))
      ($_ (PMCPProjectionRejected JudgmentMustBeApplicationV0)))))

(= (pmcp-collect-judgments $constructors $judgments LNil)
   (PMCPDeclsOK $constructors $judgments))
(= (pmcp-collect-judgments $constructors $judgments
      (LCons $pattern $rest))
   (case (pmcp-collect-judgment $constructors $judgments $pattern)
     (((PMCPDeclsOK $next-constructors $next-judgments)
        (pmcp-collect-judgments
          $next-constructors $next-judgments $rest))
      ((PMCPProjectionRejected $reason)
        (PMCPProjectionRejected $reason)))))

(= (pmcp-collect-rules $constructors $judgments LNil)
   (PMCPDeclsOK $constructors $judgments))
(= (pmcp-collect-rules $constructors $judgments
      (LCons $rule $rest))
   (case $rule
     (((GRule $id $formals $premises $conclusion)
        (case (pmcp-collect-judgments
                $constructors $judgments
                (gic-append $premises (pmcp-l1 $conclusion)))
          (((PMCPDeclsOK $next-constructors $next-judgments)
            (pmcp-collect-rules
              $next-constructors $next-judgments $rest))
           ((PMCPProjectionRejected $reason)
             (PMCPProjectionRejected $reason)))))
      ($_ (PMCPProjectionRejected MalformedRuleV0)))))

(= (pmcp-project-rules $rules)
   (case (pmcp-collect-rules LNil LNil $rules)
     (((PMCPDeclsOK $constructors $judgments)
        (PMCPProjected
          (GPresentation $constructors $judgments $rules)))
      ((PMCPProjectionRejected $reason)
        (PMCPProjectionRejected $reason)))))

; ---------- Reference and exact-cache operations ----------------------------
; V1 is the sole authored package representation in this experiment.  The
; conversion ledger contains ordinary generic rules for a declared conversion
; judgment; the generic checker receives their ordered append and has no
; conversion-specific branch.
(= (pmcp-package-v1 $rules $conversions)
   (PrimeRulePackageV1
     "prime-rule-package-v1" "prime" "0.5" $rules $conversions))

(= (pmcp-package-rules
      (PrimeRulePackageV1
        "prime-rule-package-v1" "prime" "0.5" $rules $conversions))
   (gic-append $rules $conversions))

(= (pmcp-project-package $package)
   (case $package
     (((PrimeRulePackageV1
          "prime-rule-package-v1" "prime" "0.5" $rules $conversions)
        (pmcp-project-rules (gic-append $rules $conversions)))
      ($_ (PMCPProjectionRejected InvalidPackageMetadataV1)))))

(= (pmcp-package-valid $package)
   (case $package
     (((PrimeRulePackageV1
          "prime-rule-package-v1" "prime" "0.5" $rules $conversions)
        (case (pmcp-project-rules (gic-append $rules $conversions))
          (((PMCPProjected $presentation)
            (gic-presentation-valid $presentation))
           ($_ False))))
      ($_ False))))

(= (pmcp-cache-valid $package $cached)
   (case $package
     (((PrimeRulePackageV1
          "prime-rule-package-v1" "prime" "0.5" $rules $conversions)
        (case (pmcp-project-rules (gic-append $rules $conversions))
          (((PMCPProjected $reference)
            (if (== $reference $cached)
              (gic-presentation-valid $cached)
              False))
           ($_ False))))
      ($_ False))))

(= (pmcp-check-reference $package $goal $proof)
   (case $package
     (((PrimeRulePackageV1
          "prime-rule-package-v1" "prime" "0.5" $rules $conversions)
        (case (pmcp-project-rules (gic-append $rules $conversions))
          (((PMCPProjected $presentation)
            (gic-check $presentation $goal $proof))
           ($_ False))))
      ($_ False))))

(= (pmcp-check-cached $package $cached $goal $proof)
   (if (pmcp-cache-valid $package $cached)
     (gic-check $cached $goal $proof)
     False))

; One cache comparison authorizes one whole finite batch; no reusable admission
; token is exposed.
(= (pmcp-check-cached-batch $package $cached $checks)
   (if (pmcp-cache-valid $package $cached)
     (gic-check-batch $cached $checks)
     False))

(= (pmcp-replay-report $package $goal $proof)
   (if (pmcp-check-reference $package $goal $proof)
     (PrimeReplayReportV0 CertificateAcceptedV0 CompleteV0)
     (PrimeReplayReportV0 CertificateRejectedV0 CompleteV0)))

; ---------- Modus-ponens package and literal cache --------------------------
(= (pmcp-A) (PApp "pmcp.A" LNil))
(= (pmcp-B) (PApp "pmcp.B" LNil))
(= (pmcp-Imp $left $right) (PApp "pmcp.Imp" (pmcp-l2 $left $right)))
(= (pmcp-Proves $formula) (PApp "pmcp.Proves" (pmcp-l1 $formula)))

(= (pmcp-mp-rules)
   (pmcp-l3
     (GRule "pmcp.ax-a" LNil LNil (pmcp-Proves (pmcp-A)))
     (GRule "pmcp.ax-imp" LNil LNil
       (pmcp-Proves (pmcp-Imp (pmcp-A) (pmcp-B))))
     (GRule "pmcp.mp"
       (pmcp-l2 (Formal "antecedent" 0) (Formal "consequent" 0))
       (pmcp-l2
         (pmcp-Proves (FVar "antecedent"))
         (pmcp-Proves
           (pmcp-Imp (FVar "antecedent") (FVar "consequent"))))
       (pmcp-Proves (FVar "consequent")))))

(= (pmcp-mp-package) (pmcp-package-v1 (pmcp-mp-rules) LNil))

; This cache is written independently rather than defined through projection.
(= (pmcp-mp-cache)
   (GPresentation
     (pmcp-l3
       (CDecl "pmcp.A" 0)
       (CDecl "pmcp.Imp" 2)
       (CDecl "pmcp.B" 0))
     (pmcp-l1 (JDecl "pmcp.Proves" 1))
     (pmcp-mp-rules)))

(= (pmcp-proof-a)
   (GProof (GRuleInst "pmcp.ax-a" LNil) PrNil))
(= (pmcp-proof-imp)
   (GProof (GRuleInst "pmcp.ax-imp" LNil) PrNil))
(= (pmcp-proof-b)
   (GProof
     (GRuleInst "pmcp.mp" (pmcp-l2 (pmcp-A) (pmcp-B)))
     (pmcp-pr2 (pmcp-proof-a) (pmcp-proof-imp))))

; ---------- Small DTT-shaped package ----------------------------------------
(= (pmcp-dtt-CtxNil) (PApp "pmcp.dtt.CtxNil" LNil))
(= (pmcp-dtt-Nat) (PApp "pmcp.dtt.Nat" LNil))
(= (pmcp-dtt-Z) (PApp "pmcp.dtt.Z" LNil))
(= (pmcp-dtt-Id) (PApp "pmcp.dtt.id" LNil))
(= (pmcp-dtt-Pi $a $b) (PApp "pmcp.dtt.Pi" (pmcp-l2 $a $b)))
(= (pmcp-dtt-App $f $x) (PApp "pmcp.dtt.App" (pmcp-l2 $f $x)))
(= (pmcp-dtt-HasType $ctx $term $type)
   (PApp "pmcp.dtt.HasType" (pmcp-l3 $ctx $term $type)))

(= (pmcp-dtt-rules)
   (pmcp-l3
     (GRule "pmcp.dtt.z" LNil LNil
       (pmcp-dtt-HasType
         (pmcp-dtt-CtxNil) (pmcp-dtt-Z) (pmcp-dtt-Nat)))
     (GRule "pmcp.dtt.id" LNil LNil
       (pmcp-dtt-HasType
         (pmcp-dtt-CtxNil) (pmcp-dtt-Id)
         (pmcp-dtt-Pi (pmcp-dtt-Nat) (pmcp-dtt-Nat))))
     (GRule "pmcp.dtt.app"
       (pmcp-l4
         (Formal "function" 0) (Formal "argument" 0)
         (Formal "domain" 0) (Formal "codomain" 0))
       (pmcp-l2
         (pmcp-dtt-HasType
           (pmcp-dtt-CtxNil) (FVar "function")
           (pmcp-dtt-Pi (FVar "domain") (FVar "codomain")))
         (pmcp-dtt-HasType
           (pmcp-dtt-CtxNil) (FVar "argument") (FVar "domain")))
       (pmcp-dtt-HasType
         (pmcp-dtt-CtxNil)
         (pmcp-dtt-App (FVar "function") (FVar "argument"))
         (FVar "codomain")))))

(= (pmcp-dtt-package) (pmcp-package-v1 (pmcp-dtt-rules) LNil))
(= (pmcp-dtt-cache)
   (GPresentation
     (LCons (CDecl "pmcp.dtt.CtxNil" 0)
       (LCons (CDecl "pmcp.dtt.Z" 0)
         (LCons (CDecl "pmcp.dtt.Nat" 0)
           (LCons (CDecl "pmcp.dtt.id" 0)
             (LCons (CDecl "pmcp.dtt.Pi" 2)
               (LCons (CDecl "pmcp.dtt.App" 2) LNil))))))
     (pmcp-l1 (JDecl "pmcp.dtt.HasType" 3))
     (pmcp-dtt-rules)))
(= (pmcp-dtt-proof-z)
   (GProof (GRuleInst "pmcp.dtt.z" LNil) PrNil))
(= (pmcp-dtt-proof-id)
   (GProof (GRuleInst "pmcp.dtt.id" LNil) PrNil))
(= (pmcp-dtt-proof-id-z)
   (GProof
     (GRuleInst "pmcp.dtt.app"
       (pmcp-l4
         (pmcp-dtt-Id) (pmcp-dtt-Z)
         (pmcp-dtt-Nat) (pmcp-dtt-Nat)))
     (pmcp-pr2 (pmcp-dtt-proof-id) (pmcp-dtt-proof-z))))
(= (pmcp-dtt-id-z-goal)
   (pmcp-dtt-HasType
     (pmcp-dtt-CtxNil)
     (pmcp-dtt-App (pmcp-dtt-Id) (pmcp-dtt-Z))
     (pmcp-dtt-Nat)))

; ---------- Native HOTG-shaped package --------------------------------------
(= (pmcp-hotg-N) (PApp "pmcp.hotg.N" LNil))
(= (pmcp-hotg-Power $x) (PApp "pmcp.hotg.Power" (pmcp-l1 $x)))
(= (pmcp-hotg-UnivOf $x) (PApp "pmcp.hotg.UnivOf" (pmcp-l1 $x)))
(= (pmcp-hotg-In $x $u) (PApp "pmcp.hotg.In" (pmcp-l2 $x $u)))
(= (pmcp-hotg-ZFClosed $u) (PApp "pmcp.hotg.ZFClosed" (pmcp-l1 $u)))
(= (pmcp-hotg-Proves $proposition)
   (PApp "pmcp.hotg.Proves" (pmcp-l1 $proposition)))

(= (pmcp-hotg-rules)
   (pmcp-l3
     (GRule "pmcp.hotg.univ-in" (pmcp-l1 (Formal "N" 0)) LNil
       (pmcp-hotg-Proves
         (pmcp-hotg-In (FVar "N") (pmcp-hotg-UnivOf (FVar "N")))))
     (GRule "pmcp.hotg.univ-zf" (pmcp-l1 (Formal "N" 0)) LNil
       (pmcp-hotg-Proves
         (pmcp-hotg-ZFClosed (pmcp-hotg-UnivOf (FVar "N")))))
     (GRule "pmcp.hotg.power-closed"
       (pmcp-l2 (Formal "U" 0) (Formal "X" 0))
       (pmcp-l2
         (pmcp-hotg-Proves (pmcp-hotg-ZFClosed (FVar "U")))
         (pmcp-hotg-Proves (pmcp-hotg-In (FVar "X") (FVar "U"))))
       (pmcp-hotg-Proves
         (pmcp-hotg-In (pmcp-hotg-Power (FVar "X")) (FVar "U"))))))

(= (pmcp-hotg-package) (pmcp-package-v1 (pmcp-hotg-rules) LNil))
(= (pmcp-hotg-cache)
   (GPresentation
     (pmcp-l4
       (CDecl "pmcp.hotg.In" 2)
       (CDecl "pmcp.hotg.UnivOf" 1)
       (CDecl "pmcp.hotg.ZFClosed" 1)
       (CDecl "pmcp.hotg.Power" 1))
     (pmcp-l1 (JDecl "pmcp.hotg.Proves" 1))
     (pmcp-hotg-rules)))
(= (pmcp-hotg-proof-in)
   (GProof
     (GRuleInst "pmcp.hotg.univ-in" (pmcp-l1 (pmcp-hotg-N))) PrNil))
(= (pmcp-hotg-proof-zf)
   (GProof
     (GRuleInst "pmcp.hotg.univ-zf" (pmcp-l1 (pmcp-hotg-N))) PrNil))
(= (pmcp-hotg-proof-power)
   (GProof
     (GRuleInst "pmcp.hotg.power-closed"
       (pmcp-l2 (pmcp-hotg-UnivOf (pmcp-hotg-N)) (pmcp-hotg-N)))
     (pmcp-pr2 (pmcp-hotg-proof-zf) (pmcp-hotg-proof-in))))
(= (pmcp-hotg-power-goal)
   (pmcp-hotg-Proves
     (pmcp-hotg-In
       (pmcp-hotg-Power (pmcp-hotg-N))
       (pmcp-hotg-UnivOf (pmcp-hotg-N)))))

; ---------- A deliberately contradictory local package ---------------------
(= (pmcp-bottom) (PApp "pmcp.local.Bottom" LNil))
(= (pmcp-local-proves $x) (PApp "pmcp.local.Proves" (pmcp-l1 $x)))
(= (pmcp-bottom-package)
   (pmcp-package-v1
     (pmcp-l1
       (GRule "pmcp.local.ax-bottom" LNil LNil
         (pmcp-local-proves (pmcp-bottom))))
     LNil))
(= (pmcp-bottom-proof)
   (GProof (GRuleInst "pmcp.local.ax-bottom" LNil) PrNil))

; ---------- Adversarial cache and projection fixtures -----------------------
(= (pmcp-cache-wrong-arity)
   (GPresentation
     (pmcp-l3
       (CDecl "pmcp.A" 1)
       (CDecl "pmcp.Imp" 2)
       (CDecl "pmcp.B" 0))
     (pmcp-l1 (JDecl "pmcp.Proves" 1))
     (pmcp-mp-rules)))

(= (pmcp-cache-missing-judgment)
   (GPresentation
     (pmcp-l3
       (CDecl "pmcp.A" 0)
       (CDecl "pmcp.Imp" 2)
       (CDecl "pmcp.B" 0))
     LNil
     (pmcp-mp-rules)))

(= (pmcp-cache-mutated-rule)
   (GPresentation
     (pmcp-l3
       (CDecl "pmcp.A" 0)
       (CDecl "pmcp.Imp" 2)
       (CDecl "pmcp.B" 0))
     (pmcp-l1 (JDecl "pmcp.Proves" 1))
     (pmcp-l3
       (GRule "pmcp.ax-a" LNil LNil (pmcp-Proves (pmcp-A)))
       (GRule "pmcp.ax-imp" LNil LNil
         (pmcp-Proves (pmcp-Imp (pmcp-A) (pmcp-B))))
       (GRule "pmcp.mp"
         (pmcp-l2 (Formal "antecedent" 0) (Formal "consequent" 0))
         (pmcp-l2
           (pmcp-Proves (FVar "antecedent"))
           (pmcp-Proves
             (pmcp-Imp (FVar "antecedent") (FVar "consequent"))))
         (pmcp-Proves (FVar "antecedent"))))))

(= (pmcp-conflicting-rules)
   (pmcp-l2
     (GRule "pmcp.conflict.zero" LNil LNil
       (pmcp-Proves (PApp "pmcp.conflict.F" LNil)))
     (GRule "pmcp.conflict.one" LNil LNil
       (pmcp-Proves
         (PApp "pmcp.conflict.F" (pmcp-l1 (pmcp-A)))))))

; ---------- Executable gates -------------------------------------------------
!(assertEqual
   (pmcp-project-rules (pmcp-mp-rules))
   (PMCPProjected (pmcp-mp-cache)))
!(assertEqual (pmcp-package-valid (pmcp-mp-package)) True)
!(assertEqual
   (pmcp-check-reference
     (pmcp-mp-package) (pmcp-Proves (pmcp-B)) (pmcp-proof-b))
   True)
!(assertEqual
   (pmcp-check-reference
     (pmcp-mp-package) (pmcp-Proves (pmcp-A)) (pmcp-proof-b))
   False)
!(assertEqual (pmcp-cache-valid (pmcp-mp-package) (pmcp-mp-cache)) True)
!(assertEqual
   (pmcp-check-cached
     (pmcp-mp-package) (pmcp-mp-cache)
     (pmcp-Proves (pmcp-B)) (pmcp-proof-b))
   True)
!(assertEqual
   (pmcp-cache-valid (pmcp-mp-package) (pmcp-cache-wrong-arity))
   False)
!(assertEqual
   (pmcp-cache-valid (pmcp-mp-package) (pmcp-cache-missing-judgment))
   False)
!(assertEqual
   (pmcp-cache-valid (pmcp-mp-package) (pmcp-cache-mutated-rule))
   False)
!(assertEqual
   (pmcp-check-reference
     (pmcp-dtt-package) (pmcp-dtt-id-z-goal) (pmcp-dtt-proof-id-z))
   True)
!(assertEqual
   (pmcp-project-rules (pmcp-dtt-rules))
   (PMCPProjected (pmcp-dtt-cache)))
!(assertEqual
   (pmcp-check-cached
     (pmcp-dtt-package) (pmcp-dtt-cache)
     (pmcp-dtt-id-z-goal) (pmcp-dtt-proof-id-z))
   True)
!(assertEqual
   (pmcp-check-reference
     (pmcp-hotg-package) (pmcp-hotg-power-goal) (pmcp-hotg-proof-power))
   True)
!(assertEqual
   (pmcp-project-rules (pmcp-hotg-rules))
   (PMCPProjected (pmcp-hotg-cache)))
!(assertEqual
   (pmcp-check-cached
     (pmcp-hotg-package) (pmcp-hotg-cache)
     (pmcp-hotg-power-goal) (pmcp-hotg-proof-power))
   True)
!(assertEqual
   (pmcp-check-reference
     (pmcp-dtt-package) (pmcp-dtt-id-z-goal) (pmcp-hotg-proof-power))
   False)
!(assertEqual
   (pmcp-check-reference
     (pmcp-hotg-package) (pmcp-hotg-power-goal) (pmcp-dtt-proof-id-z))
   False)
!(assertEqual
   (pmcp-check-reference
     (pmcp-bottom-package)
     (pmcp-local-proves (pmcp-bottom)) (pmcp-bottom-proof))
   True)
!(assertEqual
   (pmcp-check-reference
     (pmcp-mp-package) (pmcp-local-proves (pmcp-bottom))
     (pmcp-bottom-proof))
   False)
!(assertEqual
   (pmcp-check-cached-batch
     (pmcp-mp-package) (pmcp-mp-cache)
     (CheckCons
       (GCheck (pmcp-Proves (pmcp-B)) (pmcp-proof-b) True)
       (CheckCons
         (GCheck (pmcp-Proves (pmcp-A)) (pmcp-proof-b) False)
         CheckNil)))
   True)
!(assertEqual
   (pmcp-project-rules (pmcp-conflicting-rules))
   (PMCPProjectionRejected ConstructorArityConflictV0))
!(assertEqual
   (pmcp-replay-report
     (pmcp-mp-package) (pmcp-Proves (pmcp-B)) (pmcp-proof-b))
   (PrimeReplayReportV0 CertificateAcceptedV0 CompleteV0))

!(assertEqual
   (pmcp-replay-report
     (pmcp-mp-package) (pmcp-Proves (pmcp-A)) (pmcp-proof-b))
   (PrimeReplayReportV0 CertificateRejectedV0 CompleteV0))

!(println! (PrimeMinimalCheckingSummary 23 23 0))
