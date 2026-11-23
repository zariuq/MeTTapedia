; Generic operations on the canonical open-proof carrier. Rule schemas and
; their side conditions are interpreted by the existing generic checker.
; Mathematical references: CertificateGSLTOpenChecker, RawSubstitution and
; OpenApplication. Execution correspondence is qualified on encoded inputs.
!(import! &self gslt_checked_source_v1)

(= (gor-check-open $rules $context $goal $proof)
   (case $proof
     (((GOpenHyp $index)
       (case (gic-list-get $context $index)
         (((GICListValue $expected) (== $expected $goal))
          ($_ False))))
      ((GProof $instance $children)
       (case (gic-instantiate-rule $rules $instance)
         (((RuleOK $premises $conclusion)
           (if (== $goal $conclusion)
             (gor-check-children $rules $context $premises $children)
             False))
          ($_ False))))
      ($_ False))))

(= (gor-check-children $rules $context $premises $children)
   (case (GICPair $premises $children)
     (((GICPair LNil PrNil) True)
      ((GICPair (LCons $goal $goals) (PrCons $proof $proofs))
       (if (gor-check-open $rules $context $goal $proof)
         (gor-check-children $rules $context $goals $proofs)
         False))
      ($_ False))))

(= (gor-proof-get PrNil $index) GICNoListValue)
(= (gor-proof-get (PrCons $first $rest) $index)
   (if (== $index 0) (GICListValue $first)
     (if (> $index 0) (gor-proof-get $rest (- $index 1)) GICNoListValue)))

; This is the existing total raw substitution: an uncovered citation stays
; a citation. Public application checks the complete argument vector first.
(= (gor-substitute $arguments $proof)
   (case $proof
     (((GOpenHyp $index)
       (case (gor-proof-get $arguments $index)
         (((GICListValue $replacement) $replacement)
          ($_ $proof))))
      ((GProof $instance $children)
       (let $substituted (gor-substitute-children $arguments $children)
         (GProof $instance $substituted)))
      ($_ GorMalformed))))

(= (gor-substitute-children $arguments PrNil) PrNil)
(= (gor-substitute-children $arguments (PrCons $first $rest))
   (let $head (gor-substitute $arguments $first)
     (let $tail (gor-substitute-children $arguments $rest)
       (PrCons $head $tail))))

(= (gor-check $language $context $goal $proof)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1 $version $constructors $judgments $rules $conversion)
         (gor-check-open $rules $context $goal $proof))
        ($_ False)))
     False))

(= (gor-apply $language $premises $ambient $goal $program $arguments)
   (if (gic-language-valid $language)
     (case $language
       (((GInferenceLanguageV1 $version $constructors $judgments $rules $conversion)
         (if (gor-check-open $rules $premises $goal $program)
           (if (gor-check-children $rules $ambient $premises $arguments)
             (let $result (gor-substitute $arguments $program)
               (Some $result))
             None)
           None))
        ($_ None)))
     None))

; An inspectable dependency manifest records full lookup results, including
; absence. Agreement is data comparison, not proof authority: the program and
; the source verdict must already have been checked before a caller reuses it.
(= (gor-manifest-open $rules $context $proof)
   (case $proof
     (((GOpenHyp $index)
       (LCons (GPremiseLookup $index (gic-list-get $context $index)) LNil))
      ((GProof (GRuleInst $id $arguments) $children)
       (LCons (GRuleLookup $id (gic-lookup-rule $rules $id))
         (gor-manifest-children $rules $context $children)))
      ($_ GorMalformed))))

(= (gor-manifest-children $rules $context PrNil) LNil)
(= (gor-manifest-children $rules $context (PrCons $first $rest))
   (gic-append (gor-manifest-open $rules $context $first)
     (gor-manifest-children $rules $context $rest)))

(= (gor-agrees-open $rules $context $manifest)
   (case $manifest
     ((LNil True)
      ((LCons (GPremiseLookup $index $recorded) $rest)
       (if (== (gic-list-get $context $index) $recorded)
         (gor-agrees-open $rules $context $rest) False))
      ((LCons (GRuleLookup $id $recorded) $rest)
       (if (== (gic-lookup-rule $rules $id) $recorded)
         (gor-agrees-open $rules $context $rest) False))
      ($_ False))))

(= (gor-manifest $language $context $proof)
   (case $language
     (((GInferenceLanguageV1 $version $constructors $judgments $rules $conversion)
       (gor-manifest-open $rules $context $proof))
      ($_ GorMalformed))))

(= (gor-agrees $language $context $manifest)
   (case $language
     (((GInferenceLanguageV1 $version $constructors $judgments $rules $conversion)
       (gor-agrees-open $rules $context $manifest))
      ($_ False))))

; Requests, rule programs and derivations have different inspectable shapes.
; These are data constructors, not seals. Every use checks the actual stored
; catalog, context, goal and evidence; a caller cannot gain authority by tags.
(= (gor-rule-value (GJudgmentRequest $language $premises $goal) $program)
   (if (gor-check $language $premises $goal $program)
     (Some (GRuleProgram $language $premises $goal $program)) None))

(= (gor-apply-value $value $ambient $arguments)
   (case $value
     (((GRuleProgram $language $premises $goal $program)
       (case (gor-apply $language $premises $ambient $goal $program $arguments)
         (((Some $result) (Some (GDerivation $language $ambient $goal $result)))
          ($_ None))))
      ($_ None))))

(= (gor-check-value $value)
   (case $value
     (((GDerivation $language $context $goal $proof)
       (gor-check $language $context $goal $proof))
      ($_ False))))

(= (gor-check-request $request $value)
   (case (GICPair $request $value)
     (((GICPair (GJudgmentRequest $language $context $goal)
          (GDerivation $actual-language $actual-context $actual-goal $proof))
       (and (== $language $actual-language)
         (and (== $context $actual-context)
           (and (== $goal $actual-goal)
                (gor-check $language $context $goal $proof)))))
      ($_ False))))

; Preorder events of an already supplied proof, matching the existing open
; proof machine. This is an observation of evidence, not a search strategy.
(= (gor-events $proof)
   (case $proof
     (((GOpenHyp $index) (LCons (GAssumptionEvent $index) LNil))
      ((GProof $instantiation $children)
       (LCons (GRuleEvent $instantiation) (gor-children-events $children)))
      ($_ GorMalformed))))
(= (gor-children-events PrNil) LNil)
(= (gor-children-events (PrCons $first $rest))
   (gic-append (gor-events $first) (gor-children-events $rest)))
(= (gor-checked-events $language $context $goal $proof)
   (if (gor-check $language $context $goal $proof)
     (Some (gor-events $proof)) None))

; Source-aware operations keep the existing complete source envelope. Its
; identity/profile data are inspected and validated, never treated as an
; authenticity oracle or a substitute for source-specific adequacy.
(= (gslt-open-rule-value-v1 (GJudgmentRequest $source $premises $goal) $program)
   (case (gslt-source-validation-v1 $source)
     ((SourceAcceptedV1
       (let (GSLTSourceV1 $identity $assumptions $profiles $language) $source
         (if (gor-check $language $premises $goal $program)
           (Some (GRuleProgram $source $premises $goal $program)) None)))
      ($declined $declined))))

(= (gslt-open-apply-value-v1 $value $ambient $arguments)
   (case $value
     (((GRuleProgram $source $premises $goal $program)
       (case (gslt-source-validation-v1 $source)
         ((SourceAcceptedV1
           (let (GSLTSourceV1 $identity $assumptions $profiles $language) $source
             (case (gor-apply $language $premises $ambient $goal $program $arguments)
               (((Some $proof) (Some (GDerivation $source $ambient $goal $proof)))
                ($_ None)))))
          ($declined $declined))))
      ($_ None))))

(= (gslt-open-check-request-v1 $request $value)
   (case (GICPair $request $value)
     (((GICPair (GJudgmentRequest $source $context $goal)
          (GDerivation $actual-source $actual-context $actual-goal $proof))
       (and (== $source $actual-source)
         (and (== $context $actual-context)
           (and (== $goal $actual-goal)
             (if (gslt-source-valid-v1 $source)
               (let (GSLTSourceV1 $identity $assumptions $profiles $language) $source
                 (gor-check $language $context $goal $proof))
               False)))))
      ($_ False))))
