; A first native Metamath calculus compiled from the checked ordered source
; ledger.  The supported slice is deliberately narrow: normal postfix proofs,
; scoped hypotheses, source assertions, and an explicit identity substitution.
; Nonempty distinct-variable contexts and compressed payloads are rejected here
; until their proof-producing elaborators are connected.

!(import! &self metamath_statement_ledger_v0)
!(import! &self str)

; ---------- Ordinary source-list utilities ---------------------------------

(= (mm-native:append Nil $right) $right)
(= (mm-native:append (Cons $head $tail) $right)
   (Cons $head (mm-native:append $tail $right)))

(= (mm-native:reverse-onto Nil $result) $result)
(= (mm-native:reverse-onto (Cons $head $tail) $result)
   (mm-native:reverse-onto $tail (Cons $head $result)))
(= (mm-native:reverse $values) (mm-native:reverse-onto $values Nil))

(= (mm-native:member $value Nil) False)
(= (mm-native:member $value (Cons $head $tail))
   (if (== $value $head)
     True
     (mm-native:member $value $tail)))

(= (mm-native:add-unique $value $values)
   (if (mm-native:member $value $values)
     $values
     (Cons $value $values)))

(= (mm-native:add-all-unique Nil $values) $values)
(= (mm-native:add-all-unique (Cons $head $tail) $values)
   (mm-native:add-all-unique $tail
     (mm-native:add-unique $head $values)))

(= (mm-native:cons-to-lcons Nil) LNil)
(= (mm-native:cons-to-lcons (Cons $head $tail))
   (LCons $head (mm-native:cons-to-lcons $tail)))

(= (mm-native:cons-to-prcons Nil) PrNil)
(= (mm-native:cons-to-prcons (Cons $head $tail))
   (PrCons $head (mm-native:cons-to-prcons $tail)))

; ---------- Canonical GIC data encoding ------------------------------------

(= (mm-native:atom $value)
   (PApp "__metamath.String" (LCons (PApp $value LNil) LNil)))

(= (mm-native:atom-list Nil) (PApp "__metamath.Nil" LNil))
(= (mm-native:atom-list (Cons $head $tail))
   (PApp "__metamath.Cons"
     (LCons (mm-native:atom $head)
       (LCons (mm-native:atom-list $tail) LNil))))

(= (mm-native:formula Nil) MMNativeMalformedFormula)
(= (mm-native:formula (Cons $typecode $body))
   (PApp "__metamath.Formula"
     (LCons (mm-native:atom $typecode)
       (LCons (mm-native:atom-list $body) LNil))))

(= (mm-native:identity-pattern
      (MMSourceIdentityV0 $revision $digest))
   (PApp "__metamath.SourceIdentity"
     (LCons (mm-native:atom $revision)
       (LCons (mm-native:atom $digest) LNil))))

(= (mm-native:binding $variable $formula)
   (PApp "__metamath.Binding"
     (LCons (mm-native:atom $variable)
       (LCons (mm-native:formula $formula) LNil))))

(= (mm-native:binding-list Nil) (PApp "__metamath.Nil" LNil))
(= (mm-native:binding-list (Cons (MMNativeBinding $variable $formula) $rest))
   (PApp "__metamath.Cons"
     (LCons (mm-native:binding $variable $formula)
       (LCons (mm-native:binding-list $rest) LNil))))

(= (mm-native:substitution $bindings)
   (PApp "__metamath.Substitution"
     (LCons (mm-native:binding-list $bindings) LNil)))

(= (mm-native:context $hypothesis-labels $dv-pairs)
   (PApp "__metamath.Context"
     (LCons (mm-native:atom-list $hypothesis-labels)
       (LCons (mm-native:atom-list $dv-pairs) LNil))))

(= (mm-native:proves $identity $formula)
   (PApp "__metamath.SourceProves"
     (LCons (mm-native:identity-pattern $identity)
       (LCons (mm-native:formula $formula) LNil))))

(= (mm-native:substitution-valid
      $identity $label $substitution)
   (PApp "__metamath.SubstitutionValid"
     (LCons (mm-native:identity-pattern $identity)
       (LCons (mm-native:atom $label)
         (LCons $substitution LNil)))))

(= (mm-native:context-valid $identity $label $context)
   (PApp "__metamath.ContextValid"
     (LCons (mm-native:identity-pattern $identity)
       (LCons (mm-native:atom $label)
         (LCons $context LNil)))))

; ---------- Source vocabulary ----------------------------------------------

(= (mm-native:statement-values
      (MMStatementConst $span $symbols))
   $symbols)
(= (mm-native:statement-values
      (MMStatementVar $span $symbols))
   $symbols)
(= (mm-native:statement-values
      (MMStatementDisjoint $span $symbols))
   $symbols)
(= (mm-native:statement-values
      (MMStatementFloat $span $label $typecode $variable))
   (Cons $label (Cons $typecode (Cons $variable Nil))))
(= (mm-native:statement-values
      (MMStatementEssential $span $label $formula))
   (Cons $label $formula))
(= (mm-native:statement-values
      (MMStatementAxiom $span $label $formula))
   (Cons $label $formula))
(= (mm-native:statement-values
      (MMStatementTheorem $span $label $formula
        (MMProofNormal $proof)))
   (Cons $label (mm-native:append $formula $proof)))
(= (mm-native:statement-values
      (MMStatementTheorem $span $label $formula
        (MMProofCompressed $header $body)))
   (Cons $label (mm-native:append $formula
     (mm-native:append $header $body))))
(= (mm-native:statement-values
      (MMStatementInclude $span $path))
   (Cons $path Nil))
(= (mm-native:statement-values (MMStatementScopeOpen $span)) Nil)
(= (mm-native:statement-values (MMStatementScopeClose $span)) Nil)

(= (mm-native:vocabulary-entries Nil $values) $values)
(= (mm-native:vocabulary-entries (Cons $entry $rest) $values)
   (mm-native:vocabulary-entries $rest
     (mm-native:add-all-unique
       (mm-native:statement-values $entry) $values)))

(= (mm-native:vocabulary
      (MMSourceIdentityV0 $revision $digest) $entries)
   (mm-native:vocabulary-entries $entries
     (Cons $digest (Cons $revision Nil))))

(= (mm-native:vocabulary-constructors Nil) LNil)
(= (mm-native:vocabulary-constructors (Cons $value $rest))
   (LCons (CDecl $value 0)
     (mm-native:vocabulary-constructors $rest)))

(= (mm-native:constructors $vocabulary)
   (LCons (CDecl "__metamath.String" 1)
     (LCons (CDecl "__metamath.Nil" 0)
       (LCons (CDecl "__metamath.Cons" 2)
         (LCons (CDecl "__metamath.Formula" 2)
           (LCons (CDecl "__metamath.SourceIdentity" 2)
             (LCons (CDecl "__metamath.Binding" 2)
               (LCons (CDecl "__metamath.Substitution" 1)
                 (LCons (CDecl "__metamath.Context" 2)
                   (mm-native:vocabulary-constructors $vocabulary))))))))))

(= (mm-native:judgments)
   (LCons (JDecl "__metamath.SourceProves" 2)
     (LCons (JDecl "__metamath.SubstitutionValid" 3)
       (LCons (JDecl "__metamath.ContextValid" 3) LNil))))

; ---------- Scoped source state --------------------------------------------

(= (mm-native:hypothesis-label
      (MMNativeFloat $label $typecode $variable)) $label)
(= (mm-native:hypothesis-label
      (MMNativeEssential $label $formula)) $label)

(= (mm-native:hypothesis-formula
      (MMNativeFloat $label $typecode $variable))
   (Cons $typecode (Cons $variable Nil)))
(= (mm-native:hypothesis-formula
      (MMNativeEssential $label $formula)) $formula)

(= (mm-native:essential-formulas Nil) Nil)
(= (mm-native:essential-formulas
      (Cons (MMNativeFloat $label $typecode $variable) $rest))
   (mm-native:essential-formulas $rest))
(= (mm-native:essential-formulas
      (Cons (MMNativeEssential $label $formula) $rest))
   (Cons $formula (mm-native:essential-formulas $rest)))

(= (mm-native:symbol-occurs-in-formulas $symbol Nil) False)
(= (mm-native:symbol-occurs-in-formulas
      $symbol (Cons $formula $rest))
   (if (mm-native:member $symbol $formula)
     True
     (mm-native:symbol-occurs-in-formulas $symbol $rest)))

(= (mm-native:mandatory-hypotheses
      Nil $assertion-formula $essential-formulas) Nil)
(= (mm-native:mandatory-hypotheses
      (Cons (MMNativeFloat $label $typecode $variable) $rest)
      $assertion-formula $essential-formulas)
   (if (or (mm-native:member $variable $assertion-formula)
           (mm-native:symbol-occurs-in-formulas
             $variable $essential-formulas))
     (Cons (MMNativeFloat $label $typecode $variable)
       (mm-native:mandatory-hypotheses
         $rest $assertion-formula $essential-formulas))
     (mm-native:mandatory-hypotheses
       $rest $assertion-formula $essential-formulas)))
(= (mm-native:mandatory-hypotheses
      (Cons (MMNativeEssential $label $formula) $rest)
      $assertion-formula $essential-formulas)
   (Cons (MMNativeEssential $label $formula)
     (mm-native:mandatory-hypotheses
       $rest $assertion-formula $essential-formulas)))

(= (mm-native:hypothesis-labels Nil) Nil)
(= (mm-native:hypothesis-labels (Cons $hypothesis $rest))
   (Cons (mm-native:hypothesis-label $hypothesis)
     (mm-native:hypothesis-labels $rest)))

(= (mm-native:hypothesis-premises $identity Nil) LNil)
(= (mm-native:hypothesis-premises
      $identity (Cons $hypothesis $rest))
   (LCons
     (mm-native:proves $identity
       (mm-native:hypothesis-formula $hypothesis))
     (mm-native:hypothesis-premises $identity $rest)))

(= (mm-native:identity-bindings Nil) Nil)
(= (mm-native:identity-bindings
      (Cons (MMNativeFloat $label $typecode $variable) $rest))
   (Cons
     (MMNativeBinding $variable
       (Cons $typecode (Cons $variable Nil)))
     (mm-native:identity-bindings $rest)))
(= (mm-native:identity-bindings
      (Cons (MMNativeEssential $label $formula) $rest))
   (mm-native:identity-bindings $rest))

(= (mm-native:leaf-rule $identity $hypothesis)
   (GRule (mm-native:hypothesis-label $hypothesis)
     LNil LNil
     (mm-native:proves $identity
       (mm-native:hypothesis-formula $hypothesis))))

(= (mm-native:leaf-rules Nil $identity) Nil)
(= (mm-native:leaf-rules (Cons $hypothesis $rest) $identity)
   (Cons (mm-native:leaf-rule $identity $hypothesis)
     (mm-native:leaf-rules $rest $identity)))

; ---------- Source-derived assertions and their local side calculus --------

(= (mm-native:substitution-rule-id $label)
   (str:concat "__metamath.identity-substitution." $label))
(= (mm-native:context-rule-id $label)
   (str:concat "__metamath.context." $label))

(= (mm-native:assertion-rules
      $identity $label $mandatory $formula)
   (let $bindings (mm-native:identity-bindings $mandatory)
     (let $substitution (mm-native:substitution $bindings)
       (let $context
         (mm-native:context
           (mm-native:hypothesis-labels $mandatory) Nil)
         (Cons
           (GRule (mm-native:substitution-rule-id $label)
             LNil LNil
             (mm-native:substitution-valid
               $identity $label $substitution))
           (Cons
             (GRule (mm-native:context-rule-id $label)
               LNil LNil
               (mm-native:context-valid $identity $label $context))
             (Cons
               (GRule $label LNil
                 (mm-native:append-lcons
                   (mm-native:hypothesis-premises $identity $mandatory)
                   (LCons
                     (mm-native:substitution-valid
                       $identity $label $substitution)
                     (LCons
                       (mm-native:context-valid
                         $identity $label $context)
                       LNil)))
                 (mm-native:proves $identity $formula))
               Nil)))))))

(= (mm-native:append-lcons LNil $right) $right)
(= (mm-native:append-lcons (LCons $head $tail) $right)
   (LCons $head (mm-native:append-lcons $tail $right)))

(= (mm-native:append-rule-groups Nil) Nil)
(= (mm-native:append-rule-groups (Cons $group $rest))
   (mm-native:append $group
     (mm-native:append-rule-groups $rest)))

; ---------- Native postfix elaboration -------------------------------------

(= (mm-native:find-hypothesis $label Nil) MMNativeNotFound)
(= (mm-native:find-hypothesis $label (Cons $hypothesis $rest))
   (if (== $label (mm-native:hypothesis-label $hypothesis))
     (MMNativeFoundHypothesis $hypothesis)
     (mm-native:find-hypothesis $label $rest)))

(= (mm-native:find-assertion $label Nil) MMNativeNotFound)
(= (mm-native:find-assertion
      $label
      (Cons (MMNativeAssertion $candidate $mandatory $formula) $rest))
   (if (== $label $candidate)
     (MMNativeFoundAssertion $mandatory $formula)
     (mm-native:find-assertion $label $rest)))

(= (mm-native:pop-premises Nil $stack $children)
   (MMNativePopped $stack $children))
(= (mm-native:pop-premises
      (Cons $expected $rest)
      (Cons (MMNativeStackEntry $actual $proof) $stack)
      $children)
   (if (== (mm-native:hypothesis-formula $expected) $actual)
     (mm-native:pop-premises $rest $stack (Cons $proof $children))
     (MMNativeElaborationError premise-formula-mismatch)))
(= (mm-native:pop-premises
      (Cons $expected $rest) Nil $children)
   (MMNativeElaborationError proof-stack-underflow))

(= (mm-native:assertion-proof
      $label $mandatory $mandatory-proofs)
   (GProof (GRuleInst $label LNil)
     (mm-native:cons-to-prcons
       (mm-native:append $mandatory-proofs
         (Cons
           (GProof
             (GRuleInst
               (mm-native:substitution-rule-id $label) LNil)
             PrNil)
           (Cons
             (GProof
               (GRuleInst (mm-native:context-rule-id $label) LNil)
               PrNil)
             Nil))))))

(= (mm-native:elaborate-label
      $active $assertions $label $stack)
   (case (mm-native:find-hypothesis $label $active)
     (((MMNativeFoundHypothesis $hypothesis)
       (MMNativeElaborationOK
         (Cons
           (MMNativeStackEntry
             (mm-native:hypothesis-formula $hypothesis)
             (GProof (GRuleInst $label LNil) PrNil))
           $stack)))
      (MMNativeNotFound
       (case (mm-native:find-assertion $label $assertions)
         (((MMNativeFoundAssertion $mandatory $formula)
           (case (mm-native:pop-premises
                   (mm-native:reverse $mandatory) $stack Nil)
             (((MMNativePopped $remaining $mandatory-proofs)
               (MMNativeElaborationOK
                 (Cons
                   (MMNativeStackEntry $formula
                     (mm-native:assertion-proof
                       $label $mandatory $mandatory-proofs))
                   $remaining)))
              ($error $error))))
          (MMNativeNotFound
           (MMNativeElaborationError unknown-proof-label))))))))

(= (mm-native:elaborate-labels
      $active $assertions Nil $stack)
   (case $stack
     (((Cons (MMNativeStackEntry $formula $proof) Nil)
       (MMNativeElaborated $formula $proof))
      ($_ (MMNativeElaborationError non-singleton-final-stack)))))
(= (mm-native:elaborate-labels
      $active $assertions (Cons $label $rest) $stack)
   (case (mm-native:elaborate-label
           $active $assertions $label $stack)
     (((MMNativeElaborationOK $next-stack)
       (mm-native:elaborate-labels
         $active $assertions $rest $next-stack))
      ($error $error))))

; ---------- Ordered-ledger compiler ----------------------------------------

(= (mm-native:compile-entries
      $identity $vocabulary $target Nil
      $scope-stack $active $dv $assertions $rule-groups)
   (MMNativeCompilationError target-theorem-not-found))

(= (mm-native:compile-entries
      $identity $vocabulary $target (Cons $entry $rest)
      $scope-stack $active $dv $assertions $rule-groups)
   (case $entry
     (((MMStatementConst $span $symbols)
       (mm-native:compile-entries
         $identity $vocabulary $target $rest
         $scope-stack $active $dv $assertions $rule-groups))
      ((MMStatementVar $span $symbols)
       (mm-native:compile-entries
         $identity $vocabulary $target $rest
         $scope-stack $active $dv $assertions $rule-groups))
      ((MMStatementDisjoint $span $symbols)
       (MMNativeCompilationError distinct-variable-slice-not-connected))
      ((MMStatementFloat $span $label $typecode $variable)
       (mm-native:compile-entries
         $identity $vocabulary $target $rest
         $scope-stack
         (mm-native:append $active
           (Cons (MMNativeFloat $label $typecode $variable) Nil))
         $dv $assertions $rule-groups))
      ((MMStatementEssential $span $label $formula)
       (mm-native:compile-entries
         $identity $vocabulary $target $rest
         $scope-stack
         (mm-native:append $active
           (Cons (MMNativeEssential $label $formula) Nil))
         $dv $assertions $rule-groups))
      ((MMStatementScopeOpen $span)
       (mm-native:compile-entries
         $identity $vocabulary $target $rest
         (Cons (MMNativeScope $active $dv) $scope-stack)
         $active $dv $assertions $rule-groups))
      ((MMStatementScopeClose $span)
       (case $scope-stack
         (((Cons (MMNativeScope $outer-active $outer-dv) $outer-scopes)
           (mm-native:compile-entries
             $identity $vocabulary $target $rest
             $outer-scopes $outer-active $outer-dv
             $assertions $rule-groups))
          ($_ (MMNativeCompilationError unmatched-scope-close)))))
      ((MMStatementAxiom $span $label $formula)
       (if (== $dv Nil)
         (let $mandatory
           (mm-native:mandatory-hypotheses
             $active $formula (mm-native:essential-formulas $active))
           (mm-native:compile-entries
             $identity $vocabulary $target $rest
             $scope-stack $active $dv
             (mm-native:append $assertions
               (Cons (MMNativeAssertion $label $mandatory $formula) Nil))
             (mm-native:append $rule-groups
               (Cons
                 (mm-native:assertion-rules
                   $identity $label $mandatory $formula)
                 Nil))))
         (MMNativeCompilationError distinct-variable-slice-not-connected)))
      ((MMStatementTheorem $span $label $formula
         (MMProofNormal $proof-labels))
       (if (== $label $target)
         (case (mm-native:elaborate-labels
                 $active $assertions $proof-labels Nil)
           (((MMNativeElaborated $proved-formula $proof)
             (if (== $proved-formula $formula)
               (let $all-rules
                 (mm-native:append
                   (mm-native:leaf-rules $active $identity)
                   (mm-native:append-rule-groups $rule-groups))
                 (let $presentation
                   (GPresentation
                     (mm-native:constructors $vocabulary)
                     (mm-native:judgments)
                     (mm-native:cons-to-lcons $all-rules))
                   (let $source
                     (GSLTSourceV1
                       (case $identity
                         (((MMSourceIdentityV0 $revision $digest)
                           (SourceIdentityV1
                             "Metamath" $revision $digest))))
                       (AssumptionLedgerV1 LNil)
                       (ProfileLedgerV1
                         (LCons
                           (SourceProfileV1
                             "native-source-calculus" "v0"
                             (PApp
                               "__metamath.NativeSourceSliceV0" LNil))
                           LNil))
                       $presentation)
                     (MMNativeSourceSlice
                       $source
                       (mm-native:proves $identity $formula)
                       $proof $label))))
               (MMNativeCompilationError target-formula-not-proved)))
            ($error $error)))
         (MMNativeCompilationError prior-theorem-slice-not-connected)))
      ((MMStatementTheorem $span $label $formula
         (MMProofCompressed $header $body))
       (if (== $label $target)
         (MMNativeCompilationError compressed-slice-not-connected)
         (MMNativeCompilationError prior-theorem-slice-not-connected)))
      ((MMStatementInclude $span $path)
       (MMNativeCompilationError include-resolution-required))
      ($_ (MMNativeCompilationError malformed-ledger-entry)))))

(= (mm-native:compile-target $ledger $target)
   (case $ledger
     (((MMCheckedStatementLedger $identity $tokens $nodes $entries)
       (let $vocabulary (mm-native:vocabulary $identity $entries)
         (mm-native:compile-entries
           $identity $vocabulary $target $entries
           Nil Nil Nil Nil Nil)))
      ((MMIncludeResolutionRequired $identity $tokens $nodes $entries)
       (MMNativeCompilationError include-resolution-required))
      ($error $error))))

(= (mm-native:check-slice $result)
   (case $result
     (((MMNativeSourceSlice $source $goal $proof $label)
       (MMNativeSourceCheck
         $label
         (gslt-source-validation-v1 $source)
         (gslt-source-check-v1 $source $goal $proof)))
      ($error $error))))
