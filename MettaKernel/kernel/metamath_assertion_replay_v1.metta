; Generic replay of Metamath assertion applications over the semantic source
; database.  Proof producers supply applications and typed substitutions; this
; library recomputes substitution, essential-hypothesis agreement, and every
; distinct-variable obligation before returning a conclusion.

!(import! &self metamath_statement_semantics_v0)

; ---------- Source database ------------------------------------------------

(= (mm-replay:database
      (MMSemanticReference $revision $digest $database))
   $database)

(= (mm-replay:objects
      (MMSemanticDatabase $dv $hypotheses $objects))
   $objects)

; ---------- Explicit substitutions ----------------------------------------

(= (mm-replay:binding-count Nil) 0)
(= (mm-replay:binding-count
      (Cons (MMReplayBinding $variable $formula) $rest))
   (+ 1 (mm-replay:binding-count $rest)))

(= (mm-replay:binding-variable-member $variable Nil) False)
(= (mm-replay:binding-variable-member
      $variable
      (Cons (MMReplayBinding $candidate $formula) $rest))
   (if (== $variable $candidate)
     True
     (mm-replay:binding-variable-member $variable $rest)))

(= (mm-replay:bindings-unique Nil $seen) True)
(= (mm-replay:bindings-unique
      (Cons (MMReplayBinding $variable $formula) $rest) $seen)
   (if (mm-semantic:member $variable $seen)
     False
     (mm-replay:bindings-unique $rest (Cons $variable $seen))))

(= (mm-replay:lookup-binding $variable Nil)
   (MMReplayBindingMissing $variable))
(= (mm-replay:lookup-binding
      $variable
      (Cons (MMReplayBinding $candidate $formula) $rest))
   (if (== $variable $candidate)
     (MMReplayBindingFound $formula)
     (mm-replay:lookup-binding $variable $rest)))

(= (mm-replay:typed-binding-valid $typecode $formula)
   (case $formula
     (((Cons (MMSemanticConstantSymbol $candidate) $body)
       (== $typecode $candidate))
      ($_ False))))

(= (mm-replay:symbol-declared
      (MMSemanticConstantSymbol $name) $objects)
   (case (mm-semantic:find-object $name $objects)
     (((MMSemanticObjectFound (MMSemanticConstant $name)) True)
      ($_ False))))
(= (mm-replay:symbol-declared
      (MMSemanticVariableSymbol $name) $objects)
   (case (mm-semantic:find-object $name $objects)
     (((MMSemanticObjectFound (MMSemanticVariable $name)) True)
      ($_ False))))

(= (mm-replay:formula-declared Nil $objects) True)
(= (mm-replay:formula-declared (Cons $symbol $rest) $objects)
   (and (mm-replay:symbol-declared $symbol $objects)
        (mm-replay:formula-declared $rest $objects)))

(= (mm-replay:bindings-declared Nil $objects) True)
(= (mm-replay:bindings-declared
      (Cons (MMReplayBinding $variable $formula) $rest) $objects)
   (and (mm-replay:formula-declared $formula $objects)
        (mm-replay:bindings-declared $rest $objects)))

; Metamath substitution replaces a variable by the body of its typed formula;
; the binding's leading typecode is not copied into the containing formula.
(= (mm-replay:substitute Nil $bindings)
   (MMReplaySubstitutionOK Nil))
(= (mm-replay:substitute
      (Cons (MMSemanticConstantSymbol $name) $rest) $bindings)
   (case (mm-replay:substitute $rest $bindings)
     (((MMReplaySubstitutionOK $tail)
       (MMReplaySubstitutionOK
         (Cons (MMSemanticConstantSymbol $name) $tail)))
      ($error $error))))
(= (mm-replay:substitute
      (Cons (MMSemanticVariableSymbol $variable) $rest) $bindings)
   (case (mm-replay:lookup-binding $variable $bindings)
     (((MMReplayBindingFound
          (Cons (MMSemanticConstantSymbol $typecode) $body))
       (case (mm-replay:substitute $rest $bindings)
         (((MMReplaySubstitutionOK $tail)
           (MMReplaySubstitutionOK
             (mm-semantic:append $body $tail)))
          ($error $error))))
      ((MMReplayBindingFound $malformed)
       (MMReplaySubstitutionError malformed-binding $variable))
      ((MMReplayBindingMissing $missing)
       (MMReplaySubstitutionError missing-binding $missing)))))

; ---------- Distinct-variable checking ------------------------------------

(= (mm-replay:variables-in-formula Nil $found) $found)
(= (mm-replay:variables-in-formula
      (Cons (MMSemanticConstantSymbol $name) $rest) $found)
   (mm-replay:variables-in-formula $rest $found))
(= (mm-replay:variables-in-formula
      (Cons (MMSemanticVariableSymbol $name) $rest) $found)
   (mm-replay:variables-in-formula $rest
     (mm-semantic:add-unique $name $found)))

(= (mm-replay:cross-dv-valid $left Nil $target-dv) True)
(= (mm-replay:cross-dv-valid
      $left (Cons $right $right-rest) $target-dv)
   (and (not (== $left $right))
     (and
       (mm-semantic:pair-member
         (MMSemanticPair $left $right) $target-dv)
       (mm-replay:cross-dv-valid $left $right-rest $target-dv))))

(= (mm-replay:all-cross-dv-valid Nil $right $target-dv) True)
(= (mm-replay:all-cross-dv-valid
      (Cons $left $left-rest) $right $target-dv)
   (and (mm-replay:cross-dv-valid $left $right $target-dv)
        (mm-replay:all-cross-dv-valid $left-rest $right $target-dv)))

(= (mm-replay:source-dv-valid Nil $bindings $target-dv) True)
(= (mm-replay:source-dv-valid
      (Cons (MMSemanticPair $left $right) $rest)
      $bindings $target-dv)
   (case (Cons (mm-replay:lookup-binding $left $bindings)
           (Cons (mm-replay:lookup-binding $right $bindings) Nil))
     (((Cons (MMReplayBindingFound $left-formula)
             (Cons (MMReplayBindingFound $right-formula) Nil))
       (and
         (mm-replay:all-cross-dv-valid
           (mm-replay:variables-in-formula $left-formula Nil)
           (mm-replay:variables-in-formula $right-formula Nil)
           $target-dv)
         (mm-replay:source-dv-valid $rest $bindings $target-dv)))
      ($_ False))))

; ---------- Target hypotheses ---------------------------------------------

(= (mm-replay:find-assumption $label Nil)
   (MMReplayAssumptionMissing $label))
(= (mm-replay:find-assumption
      $label
      (Cons (MMReplayAssumption $candidate $formula) $rest))
   (if (== $label $candidate)
     (MMReplayAssumptionFound $formula)
     (mm-replay:find-assumption $label $rest)))

; ---------- Mandatory hypotheses ------------------------------------------

(= (mm-replay:float-count Nil $objects) 0)
(= (mm-replay:float-count (Cons $label $rest) $objects)
   (case (mm-semantic:find-object $label $objects)
     (((MMSemanticObjectFound
          (MMSemanticHypothesis False $formula $source-label))
       (+ 1 (mm-replay:float-count $rest $objects)))
      ((MMSemanticObjectFound $other)
       (mm-replay:float-count $rest $objects))
      (MMSemanticObjectNotFound -1))))

; ---------- Checked proof DAG ---------------------------------------------

(= (mm-replay:find-checked-step $id Nil)
   (MMReplayCheckedStepMissing $id))
(= (mm-replay:find-checked-step
      $id (Cons (MMReplayCheckedStep $candidate $formula $step) $rest))
   (if (== $id $candidate)
     (MMReplayCheckedStepFound $formula $step)
     (mm-replay:find-checked-step $id $rest)))

(= (mm-replay:finish-essential-substitution
      $label $actual (MMReplaySubstitutionOK $expected))
   (if (== $expected $actual)
     MMReplayEssentialOK
     (MMReplayEssentialError
       (essential-mismatch $label $expected $actual))))
(= (mm-replay:finish-essential-substitution
      $label $actual (MMReplaySubstitutionError $kind $detail))
   (MMReplayEssentialError (MMReplaySubstitutionError $kind $detail)))

(= (mm-replay:finish-essential-parent
      $label $source-formula $bindings
      (MMReplayCheckedStepFound $actual $parent-step))
   (mm-replay:finish-essential-substitution
     $label $actual (mm-replay:substitute $source-formula $bindings)))
(= (mm-replay:finish-essential-parent
      $label $source-formula $bindings
      (MMReplayCheckedStepMissing $missing))
   (MMReplayEssentialError (unknown-parent $label $missing)))

(= (mm-replay:check-essential-parent
      $label $source-formula $parent-id $bindings $checked)
   (mm-replay:finish-essential-parent
     $label $source-formula $bindings
     (mm-replay:find-checked-step $parent-id $checked)))

(= (mm-replay:check-hypotheses
      Nil Nil $bindings $checked $reference)
   MMReplayHypothesesOK)
(= (mm-replay:check-hypotheses
      Nil (Cons $extra $rest) $bindings $checked $reference)
   (MMReplayHypothesesError extra-parent))
(= (mm-replay:check-hypotheses
      (Cons $label $labels) $parents $bindings $checked $reference)
   (let $objects
     (mm-replay:objects (mm-replay:database $reference))
     (mm-replay:check-hypothesis-object
       $label $labels $parents $bindings $checked $reference
       (mm-semantic:find-object $label $objects))))

(= (mm-replay:finish-float-hypothesis
      $label $labels $parents $bindings $checked $reference
      $typecode $variable (MMReplayBindingFound $formula))
   (if (mm-replay:typed-binding-valid $typecode $formula)
     (mm-replay:check-hypotheses
       $labels $parents $bindings $checked $reference)
     (MMReplayHypothesesError (wrong-binding-type $label $variable))))
(= (mm-replay:finish-float-hypothesis
      $label $labels $parents $bindings $checked $reference
      $typecode $variable (MMReplayBindingMissing $missing))
   (MMReplayHypothesesError (missing-binding $label $missing)))

(= (mm-replay:finish-essential-hypothesis
      $labels $remaining $bindings $checked $reference
      MMReplayEssentialOK)
   (mm-replay:check-hypotheses
     $labels $remaining $bindings $checked $reference))
(= (mm-replay:finish-essential-hypothesis
      $labels $remaining $bindings $checked $reference
      (MMReplayEssentialError $reason))
   (MMReplayHypothesesError $reason))

(= (mm-replay:check-hypothesis-object
      $label $labels $parents $bindings $checked $reference
      (MMSemanticObjectFound
        (MMSemanticHypothesis False
          (Cons (MMSemanticConstantSymbol $typecode)
            (Cons (MMSemanticVariableSymbol $variable) Nil))
          $source-label)))
   (mm-replay:finish-float-hypothesis
     $label $labels $parents $bindings $checked $reference
     $typecode $variable (mm-replay:lookup-binding $variable $bindings)))
(= (mm-replay:check-hypothesis-object
      $label $labels (Cons $parent-id $remaining)
      $bindings $checked $reference
      (MMSemanticObjectFound
        (MMSemanticHypothesis True $source-formula $source-label)))
   (mm-replay:finish-essential-hypothesis
     $labels $remaining $bindings $checked $reference
     (mm-replay:check-essential-parent
       $label $source-formula $parent-id $bindings $checked)))
(= (mm-replay:check-hypothesis-object
      $label $labels Nil $bindings $checked $reference
      (MMSemanticObjectFound
        (MMSemanticHypothesis True $source-formula $source-label)))
   (MMReplayHypothesesError (missing-parent $label)))
(= (mm-replay:check-hypothesis-object
      $label $labels $parents $bindings $checked $reference
      (MMSemanticObjectFound (MMSemanticConstant $name)))
   (MMReplayHypothesesError (mandatory-label-not-hypothesis $label)))
(= (mm-replay:check-hypothesis-object
      $label $labels $parents $bindings $checked $reference
      (MMSemanticObjectFound (MMSemanticVariable $name)))
   (MMReplayHypothesesError (mandatory-label-not-hypothesis $label)))
(= (mm-replay:check-hypothesis-object
      $label $labels $parents $bindings $checked $reference
      (MMSemanticObjectFound
        (MMSemanticAssertion $formula $dv $hypotheses $source-label)))
   (MMReplayHypothesesError (mandatory-label-not-hypothesis $label)))
(= (mm-replay:check-hypothesis-object
      $label $labels $parents $bindings $checked $reference
      MMSemanticObjectNotFound)
   (MMReplayHypothesesError (unknown-mandatory-label $label)))

(= (mm-replay:check-application
      $label $bindings $parents
      (MMReplayContext $assumptions $target-dv) $checked $reference)
   (let $objects
     (mm-replay:objects (mm-replay:database $reference))
     (case (mm-semantic:find-object $label $objects)
       (((MMSemanticObjectFound
            (MMSemanticAssertion
              $source-formula $source-dv $mandatory $source-label))
         (if (mm-replay:bindings-unique $bindings Nil)
           (if (mm-replay:bindings-declared $bindings $objects)
             (if (== (mm-replay:binding-count $bindings)
                     (mm-replay:float-count $mandatory $objects))
               (if (mm-replay:source-dv-valid
                     $source-dv $bindings $target-dv)
                 (case (mm-replay:check-hypotheses
                         $mandatory $parents $bindings $checked $reference)
                   ((MMReplayHypothesesOK
                     (case (mm-replay:substitute $source-formula $bindings)
                       (((MMReplaySubstitutionOK $conclusion)
                         (MMReplayApplicationAccepted $conclusion))
                        ($error (MMReplayApplicationRejected $error)))))
                    ((MMReplayHypothesesError $reason)
                     (MMReplayApplicationRejected $reason))))
                 (MMReplayApplicationRejected
                   (distinct-variable-violation $label)))
               (MMReplayApplicationRejected
                 (binding-cardinality-mismatch $label)))
             (MMReplayApplicationRejected
               (undeclared-binding-symbol $label)))
           (MMReplayApplicationRejected (duplicate-binding $label))))
        ((MMSemanticObjectFound $other)
         (MMReplayApplicationRejected (proof-label-not-assertion $label)))
        (MMSemanticObjectNotFound
         (MMReplayApplicationRejected (unknown-proof-label $label)))))))

(= (mm-replay:check-step
      (MMReplayHypStep $id $label)
      (MMReplayContext $assumptions $target-dv) $checked $reference)
   (case (mm-replay:find-checked-step $id $checked)
     (((MMReplayCheckedStepMissing $missing)
       (case (mm-replay:find-assumption $label $assumptions)
         (((MMReplayAssumptionFound $formula)
           (MMReplayStepAccepted
             (MMReplayCheckedStep $id $formula
               (MMReplayHypStep $id $label))))
          ((MMReplayAssumptionMissing $missing-label)
           (MMReplayStepRejected
             (unknown-target-hypothesis $missing-label))))))
      ((MMReplayCheckedStepFound $formula $step)
       (MMReplayStepRejected (duplicate-step-id $id))))))

(= (mm-replay:finish-application-step
      $id $label $bindings $parents
      (MMReplayApplicationAccepted $formula))
   (MMReplayStepAccepted
     (MMReplayCheckedStep $id $formula
       (MMReplayApplyStep $id $label $bindings $parents))))
(= (mm-replay:finish-application-step
      $id $label $bindings $parents
      (MMReplayApplicationRejected $reason))
   (MMReplayStepRejected $reason))

(= (mm-replay:check-step
      (MMReplayApplyStep $id $label $bindings $parents)
      $context $checked $reference)
   (case (mm-replay:find-checked-step $id $checked)
     (((MMReplayCheckedStepMissing $missing)
       (mm-replay:finish-application-step
         $id $label $bindings $parents
         (mm-replay:check-application
           $label $bindings $parents $context $checked $reference)))
      ((MMReplayCheckedStepFound $formula $step)
       (MMReplayStepRejected (duplicate-step-id $id))))))

(= (mm-replay:replay-steps Nil $context $checked $reference)
   (MMReplayStepsAccepted $checked))
(= (mm-replay:replay-steps
      (Cons $step $rest) $context $checked $reference)
   (case (mm-replay:check-step $step $context $checked $reference)
     (((MMReplayStepAccepted $checked-step)
       (mm-replay:replay-steps $rest $context
         (mm-semantic:append $checked (Cons $checked-step Nil)) $reference))
      ((MMReplayStepRejected $reason)
       (MMReplayStepsRejected $reason)))))

(= (mm-replay:check-certificate
      (MMReplayCertificate $context $steps $root) $goal $reference)
   (case (mm-replay:replay-steps $steps $context Nil $reference)
     (((MMReplayStepsAccepted $checked)
       (case (mm-replay:find-checked-step $root $checked)
         (((MMReplayCheckedStepFound $actual $root-step)
           (if (== $goal $actual)
             (MMReplayGoalAccepted
               (MMReplayCertificate $context $steps $root) $goal)
             (MMReplayGoalRejected (wrong-conclusion $goal $actual))))
          ((MMReplayCheckedStepMissing $missing)
           (MMReplayGoalRejected (unknown-root $missing))))))
      ((MMReplayStepsRejected $reason)
       (MMReplayGoalRejected $reason)))))

; ---------- Source-authenticated theorem targets --------------------------

(= (mm-replay:target-assumptions Nil $objects)
   (MMReplayTargetAssumptionsOK Nil))
(= (mm-replay:target-assumptions (Cons $label $rest) $objects)
   (mm-replay:target-assumption-object
     $label $rest $objects (mm-semantic:find-object $label $objects)))

(= (mm-replay:target-assumption-object
      $label $rest $objects
      (MMSemanticObjectFound
        (MMSemanticHypothesis False $formula $source-label)))
   (mm-replay:target-assumptions $rest $objects))
(= (mm-replay:target-assumption-object
      $label $rest $objects
      (MMSemanticObjectFound
        (MMSemanticHypothesis True $formula $source-label)))
   (mm-replay:prepend-target-assumption $label $formula
     (mm-replay:target-assumptions $rest $objects)))
(= (mm-replay:target-assumption-object
      $label $rest $objects
      (MMSemanticObjectFound (MMSemanticConstant $name)))
   (MMReplayTargetAssumptionsError
     (target-mandatory-label-not-hypothesis $label)))
(= (mm-replay:target-assumption-object
      $label $rest $objects
      (MMSemanticObjectFound (MMSemanticVariable $name)))
   (MMReplayTargetAssumptionsError
     (target-mandatory-label-not-hypothesis $label)))
(= (mm-replay:target-assumption-object
      $label $rest $objects
      (MMSemanticObjectFound
        (MMSemanticAssertion $formula $dv $mandatory $source-label)))
   (MMReplayTargetAssumptionsError
     (target-mandatory-label-not-hypothesis $label)))
(= (mm-replay:target-assumption-object
      $label $rest $objects MMSemanticObjectNotFound)
   (MMReplayTargetAssumptionsError
     (unknown-target-mandatory-label $label)))

(= (mm-replay:prepend-target-assumption $label $formula
      (MMReplayTargetAssumptionsOK $rest))
   (MMReplayTargetAssumptionsOK
     (Cons (MMReplayAssumption $label $formula) $rest)))
(= (mm-replay:prepend-target-assumption $label $formula
      (MMReplayTargetAssumptionsError $reason))
   (MMReplayTargetAssumptionsError $reason))

(= (mm-replay:finish-target-context
      $label $certificate $source-formula $source-dv
      $actual-assumptions $actual-dv $reference
      (MMReplayTargetAssumptionsOK $expected-assumptions))
   (if (mm-semantic:pair-set-equal $source-dv $actual-dv)
     (if (== $expected-assumptions $actual-assumptions)
       (mm-replay:check-certificate
         $certificate $source-formula $reference)
       (MMReplayGoalRejected
         (target-assumption-context-mismatch $label)))
     (MMReplayGoalRejected (target-dv-context-mismatch $label))))
(= (mm-replay:finish-target-context
      $label $certificate $source-formula $source-dv
      $actual-assumptions $actual-dv $reference
      (MMReplayTargetAssumptionsError $reason))
   (MMReplayGoalRejected $reason))

(= (mm-replay:check-target-object
      $label $certificate $actual-assumptions $actual-dv $reference $objects
      (MMSemanticObjectFound
        (MMSemanticAssertion
          $source-formula $source-dv $mandatory $source-label)))
   (mm-replay:finish-target-context
     $label $certificate $source-formula $source-dv
     $actual-assumptions $actual-dv $reference
     (mm-replay:target-assumptions $mandatory $objects)))
(= (mm-replay:check-target-object
      $label $certificate $actual-assumptions $actual-dv $reference $objects
      (MMSemanticObjectFound (MMSemanticConstant $name)))
   (MMReplayGoalRejected (target-label-not-assertion $label)))
(= (mm-replay:check-target-object
      $label $certificate $actual-assumptions $actual-dv $reference $objects
      (MMSemanticObjectFound (MMSemanticVariable $name)))
   (MMReplayGoalRejected (target-label-not-assertion $label)))
(= (mm-replay:check-target-object
      $label $certificate $actual-assumptions $actual-dv $reference $objects
      (MMSemanticObjectFound
        (MMSemanticHypothesis $essential $formula $source-label)))
   (MMReplayGoalRejected (target-label-not-assertion $label)))
(= (mm-replay:check-target-object
      $label $certificate $actual-assumptions $actual-dv $reference $objects
      MMSemanticObjectNotFound)
   (MMReplayGoalRejected (unknown-target-label $label)))

; Public theorem acceptance authenticates the carried context against the
; theorem's source frame before ordinary certificate replay.  In particular,
; a producer cannot grant itself extra distinct-variable assumptions.
(= (mm-replay:check-theorem-certificate
      $label
      (MMReplayCertificate
        (MMReplayContext $assumptions $target-dv) $steps $root)
      $reference)
   (let $objects
     (mm-replay:objects (mm-replay:database $reference))
     (mm-replay:check-target-object
       $label
       (MMReplayCertificate
         (MMReplayContext $assumptions $target-dv) $steps $root)
       $assumptions $target-dv $reference $objects
       (mm-semantic:find-object $label $objects))))
