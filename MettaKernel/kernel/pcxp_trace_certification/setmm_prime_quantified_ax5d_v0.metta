; Authentic quantified Metamath replay for ax5d.  The proof term applies a1i
; to an ax-5 instance; replay recomputes the source substitution and the
; distinct-variable condition $d x ps before accepting the conclusion.

!(import! &self metamath_assertion_replay_v1)
!(import! &self pcxp_trace_certification/setmm_ax5d_semantic_reference_v0)

(= (ax5d:append Nil $right) $right)
(= (ax5d:append (Cons $head $tail) $right)
   (Cons $head (ax5d:append $tail $right)))

(= (ax5d:variable $name)
   (Cons (MMSemanticVariableSymbol $name) Nil))

(= (ax5d:implication $left $right)
   (Cons (MMSemanticConstantSymbol "(")
     (ax5d:append $left
       (Cons (MMSemanticConstantSymbol "->")
         (ax5d:append $right
           (Cons (MMSemanticConstantSymbol ")") Nil))))))

(= (ax5d:forall $variable $body)
   (Cons (MMSemanticConstantSymbol "A.")
     (Cons (MMSemanticVariableSymbol $variable) $body)))

(= (ax5d:wff $body)
   (Cons (MMSemanticConstantSymbol "wff") $body))
(= (ax5d:setvar $variable)
   (Cons (MMSemanticConstantSymbol "setvar")
     (Cons (MMSemanticVariableSymbol $variable) Nil)))
(= (ax5d:proves $body)
   (Cons (MMSemanticConstantSymbol "|-") $body))

(= (ax5d:ph) (ax5d:variable "ph"))
(= (ax5d:ps) (ax5d:variable "ps"))
(= (ax5d:forall-ps) (ax5d:forall "x" (ax5d:ps)))
(= (ax5d:ax5-body)
   (ax5d:implication (ax5d:ps) (ax5d:forall-ps)))
(= (ax5d:goal-body)
   (ax5d:implication (ax5d:ph) (ax5d:ax5-body)))
(= (ax5d:goal) (ax5d:proves (ax5d:goal-body)))

(= (ax5d:reference)
   (mm-semantic-reference-v0
     "94b6e5c31ab5d0c8416d136a1daaec75cc9b89690c0c62c5a24d947feccd9819"))

(= (ax5d:context)
   (MMReplayContext Nil
     (Cons (MMSemanticPair "x" "ps") Nil)))

(= (ax5d:ax-5-step $id)
   (MMReplayApplyStep $id "ax-5"
     (Cons (MMReplayBinding "ph" (ax5d:wff (ax5d:ps)))
       (Cons (MMReplayBinding "x" (ax5d:setvar "x")) Nil))
     Nil))

(= (ax5d:a1i-step $id $parent)
   (MMReplayApplyStep $id "a1i"
     (Cons (MMReplayBinding "ph" (ax5d:wff (ax5d:ax5-body)))
       (Cons (MMReplayBinding "ps" (ax5d:wff (ax5d:ph))) Nil))
     (Cons $parent Nil)))

(= (ax5d:certificate $context)
   (MMReplayCertificate $context
     (Cons (ax5d:ax-5-step "ax5")
       (Cons (ax5d:a1i-step "root" "ax5") Nil))
     "root"))

(= (ax5d:expect-accepted $name $result)
   (case $result
     (((MMReplayGoalAccepted $proof $goal) (PASS $name))
      ($_ (FAIL $name $result)))))

(= (ax5d:expect-rejected $name $result)
   (case $result
     (((MMReplayGoalRejected $reason) (PASS $name $reason))
      ($_ (FAIL $name $result)))))

; The logical proof DAG represented by the stored ax5d compressed derivation.
!(ax5d:expect-accepted authentic-ax5d
   (mm-replay:check-theorem-certificate "ax5d"
     (ax5d:certificate (ax5d:context))
     (ax5d:reference)))

; Removing the theorem-frame DV pair invalidates the ax-5 application.
!(ax5d:expect-rejected missing-target-dv
   (mm-replay:check-theorem-certificate "ax5d"
     (ax5d:certificate (MMReplayContext Nil Nil))
     (ax5d:reference)))

; A substituted formula containing the quantified variable creates x/x in
; the source-DV cross-product and must be rejected.
!(ax5d:expect-rejected captured-variable
   (let $captured (ax5d:forall "x" (ax5d:ps))
     (mm-replay:check-theorem-certificate "ax5d"
       (MMReplayCertificate (ax5d:context)
         (Cons
           (MMReplayApplyStep "root" "ax-5"
             (Cons (MMReplayBinding "ph" (ax5d:wff $captured))
               (Cons (MMReplayBinding "x" (ax5d:setvar "x")) Nil))
             Nil)
           Nil)
         "root")
       (ax5d:reference))))

; Replacing x by y requires $d y ps, which is absent from the target frame.
!(ax5d:expect-rejected wrong-quantified-variable
   (mm-replay:check-theorem-certificate "ax5d"
     (MMReplayCertificate (ax5d:context)
       (Cons
         (MMReplayApplyStep "root" "ax-5"
           (Cons (MMReplayBinding "ph" (ax5d:wff (ax5d:ps)))
             (Cons (MMReplayBinding "x" (ax5d:setvar "y")) Nil))
           Nil)
         Nil)
       "root")
     (ax5d:reference)))

; A different proof parent cannot satisfy a1i's essential hypothesis.
!(ax5d:expect-rejected mutated-proof-parent
   (mm-replay:check-theorem-certificate "ax5d"
     (MMReplayCertificate (ax5d:context)
       (Cons (ax5d:ax-5-step "ax5")
         (Cons (ax5d:a1i-step "root" "missing") Nil))
       "root")
     (ax5d:reference)))

; Changing the outer substitution makes the checked child disagree with a1i.1.
!(ax5d:expect-rejected mutated-substitution
   (let $mutated-root
     (MMReplayApplyStep "root" "a1i"
       (Cons (MMReplayBinding "ph" (ax5d:wff (ax5d:ps)))
         (Cons (MMReplayBinding "ps" (ax5d:wff (ax5d:ph))) Nil))
       (Cons "ax5" Nil))
     (mm-replay:check-theorem-certificate "ax5d"
       (MMReplayCertificate (ax5d:context)
         (Cons (ax5d:ax-5-step "ax5")
           (Cons $mutated-root Nil))
         "root")
       (ax5d:reference))))

; Duplicate bindings and symbols outside the source database are rejected
; before assertion replay.
!(ax5d:expect-rejected duplicate-binding
   (let $duplicate
     (MMReplayApplyStep "root" "ax-5"
       (Cons (MMReplayBinding "ph" (ax5d:wff (ax5d:ps)))
         (Cons (MMReplayBinding "ph" (ax5d:wff (ax5d:ph))) Nil))
       Nil)
     (mm-replay:check-theorem-certificate "ax5d"
       (MMReplayCertificate (ax5d:context) (Cons $duplicate Nil) "root")
       (ax5d:reference))))

!(ax5d:expect-rejected undeclared-symbol
   (let $undeclared
     (MMReplayApplyStep "root" "ax-5"
       (Cons (MMReplayBinding "ph" (ax5d:wff (ax5d:ps)))
         (Cons (MMReplayBinding "x" (ax5d:setvar "z")) Nil))
       Nil)
     (mm-replay:check-theorem-certificate "ax5d"
       (MMReplayCertificate (ax5d:context) (Cons $undeclared Nil) "root")
       (ax5d:reference))))

; A certificate cannot grant itself additional target-frame DV assumptions.
!(ax5d:expect-rejected forged-target-dv-context
   (let $forged-context
     (MMReplayContext Nil
       (Cons (MMSemanticPair "x" "ps")
         (Cons (MMSemanticPair "y" "ps") Nil)))
     (mm-replay:check-theorem-certificate "ax5d"
       (ax5d:certificate $forged-context)
       (ax5d:reference))))

; Target essential hypotheses are source data too; ax5d has none.
!(ax5d:expect-rejected forged-target-assumption-context
   (let $forged-context
     (MMReplayContext
       (Cons (MMReplayAssumption "forged" (ax5d:proves (ax5d:ps))) Nil)
       (Cons (MMSemanticPair "x" "ps") Nil))
     (mm-replay:check-theorem-certificate "ax5d"
       (ax5d:certificate $forged-context)
       (ax5d:reference))))

!(SetMMPrimeQuantifiedAx5dSummary replay 1 rejected-mutations 9)
