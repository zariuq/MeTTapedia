import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

/-!
# Executing an authored rule with retained binding contexts

This entry point consumes the original rule and its optional binding
declaration. Matching returns contextual values; the existing ordered premise
machine can contribute root-context outputs; the exact authored RHS is then
instantiated from the completed assignment. Missing contextual data declines
execution. A further premise interpreter is needed for occurrences whose
dependency spines are nonempty inside a premise.
-/

namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

set_option autoImplicit false

/-- The existing premise machine runs at the rule root. A premise that opens
its own binder needs a contextual premise interpreter before it can supply
values to this route. -/
def rootPremiseShape : Premise → Bool
  | .freshness condition => Match.binderFree condition.term
  | .congruence source target =>
      Match.binderFree source && Match.binderFree target
  | .scopedStep step =>
      step.binders.isEmpty &&
        Match.binderFree step.source && Match.binderFree step.target
  | .relationQuery _ arguments => arguments.all Match.binderFree
  | .forAll _ _ _ => false

/-- Explicit occurrence substitutions inside premises need interpretation by
the premise machine itself; the root adapter has no such action. -/
def noPremiseOccurrenceArguments (spec : RuleBindingSpec) : Bool :=
  spec.occurrences.all fun row =>
    match row.site with
    | .premise _ _ _ => false
    | _ => true

/-- The precise currently executable profile of an authored presentation:
validated binding declarations, root-context premises, and no occurrence
substitutions inside premises. Richer premise forms are deliberately outside
this interpreter until their contextual semantics is supplied. -/
def scopedRewritesExecutable (lang : LanguageDef) : Bool :=
  bindingDeclarationsValid lang && lang.rewrites.all fun rule =>
    rule.premises.all rootPremiseShape &&
      match rule.bindings with
      | none => false
      | some spec => noPremiseOccurrenceArguments spec

/-- The presentation-level check makes the binding and premise restrictions
available separately for each authored rule. -/
theorem scopedRewritesExecutable_rule {lang : LanguageDef}
    (hready : scopedRewritesExecutable lang = true) {rule : RewriteRule}
    (hmem : rule ∈ lang.rewrites) :
    ∃ spec, rule.bindings = some spec ∧ admittedFor rule spec = true ∧
      dependencySortsDeclared lang spec = true ∧
      rule.premises.all rootPremiseShape = true ∧
      noPremiseOccurrenceArguments spec = true := by
  simp only [scopedRewritesExecutable, Bool.and_eq_true] at hready
  obtain ⟨spec, hspec, hadmitted, hsorts⟩ :=
    bindingDeclarationsValid_rule hready.1 hmem
  have hrule := List.all_eq_true.mp hready.2 rule hmem
  rw [hspec] at hrule
  simp only [Bool.and_eq_true] at hrule
  exact ⟨spec, hspec, hadmitted, hsorts, hrule.1, hrule.2⟩

/-- Retain the captured assignment for an unconditional rule. For an ordered
premise list, reconcile every result of the existing premise interpreter. -/
def completeAssignments (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (captured : Assignment) : List Assignment :=
  match rule.premises with
  | [] => [captured]
  | _ =>
      if rule.premises.all rootPremiseShape && noPremiseOccurrenceArguments spec then
        match projectRoot? ambient captured with
        | none => []
        | some root =>
            (applyPremisesWithEnv relEnv lang rule.premises root).filterMap
              (extendRoot? spec ambient captured)
      else []

/-- Execute one rule in an explicit ambient de Bruijn context. The returned
list retains matching and premise occurrences. -/
def applyRuleComparedWithAt (compare : String → Pattern → Pattern → Bool)
    (operation : Pattern → Pattern → Pattern)
    (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (rule : RewriteRule) (term : Pattern) : List Pattern :=
  match rule.bindings with
  | none => []
  | some spec =>
      if admittedFor rule spec then
        (matchRuleWithAt compare rule spec ambient term).flatMap fun captured =>
          (completeAssignments relEnv lang ambient rule spec captured).filterMap
            (reductWith? operation rule spec ambient)
      else []

/-- Literal comparison specializes the same contextual execution pipeline. -/
def applyRuleWithAt (operation : Pattern → Pattern → Pattern)
    (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (rule : RewriteRule) (term : Pattern) : List Pattern :=
  applyRuleComparedWithAt literalBodyComparison operation relEnv lang ambient rule term

/-- Ordinary execution specializes the same matching and premise pipeline. -/
def applyRuleAt (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (rule : RewriteRule) (term : Pattern) : List Pattern :=
  applyRuleWithAt Substitution.instantiateBVar relEnv lang ambient rule term

/-- The execution is exactly the sequence of completed scoped assignments
produced by the matcher and the ordered premise machine. -/
theorem mem_applyRuleComparedWithAt_iff (compare : String → Pattern → Pattern → Bool)
    (operation : Pattern → Pattern → Pattern)
    (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (rule : RewriteRule) (term result : Pattern) :
    result ∈ applyRuleComparedWithAt compare operation relEnv lang ambient rule term ↔
      ∃ spec captured assignment,
        rule.bindings = some spec ∧
        admittedFor rule spec = true ∧
        captured ∈ matchRuleWithAt compare rule spec ambient term ∧
        assignment ∈ completeAssignments relEnv lang ambient rule spec captured ∧
        reductWith? operation rule spec ambient assignment = some result := by
  cases hspec : rule.bindings with
  | none => simp [applyRuleComparedWithAt, hspec]
  | some spec =>
      by_cases hvalid : admittedFor rule spec = true
      · simp only [applyRuleComparedWithAt, hspec, hvalid, if_true, List.mem_flatMap]
        constructor
        · rintro ⟨captured, hcaptured, hresult⟩
          obtain ⟨assignment, hcompleted, hresult⟩ :=
            List.mem_filterMap.mp hresult
          exact ⟨spec, captured, assignment, rfl, hvalid,
            hcaptured, hcompleted, hresult⟩
        · rintro ⟨chosen, captured, assignment,
            hchosen, _, hcaptured, hcompleted, hresult⟩
          cases Option.some.inj hchosen
          exact ⟨captured, hcaptured,
            List.mem_filterMap.mpr ⟨assignment, hcompleted, hresult⟩⟩
      · have hfalse : admittedFor rule spec = false := Bool.eq_false_iff.mpr hvalid
        simp [applyRuleComparedWithAt, hspec, hfalse]

theorem mem_applyRuleWithAt_iff (operation : Pattern → Pattern → Pattern)
    (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (rule : RewriteRule) (term result : Pattern) :
    result ∈ applyRuleWithAt operation relEnv lang ambient rule term ↔
      ∃ spec captured assignment,
        rule.bindings = some spec ∧
        admittedFor rule spec = true ∧
        captured ∈ matchRuleAt rule spec ambient term ∧
        assignment ∈ completeAssignments relEnv lang ambient rule spec captured ∧
        reductWith? operation rule spec ambient assignment = some result :=
  mem_applyRuleComparedWithAt_iff literalBodyComparison operation relEnv lang ambient rule term result

/-- Ordinary execution retains the same exact assignment witnesses. -/
theorem mem_applyRuleAt_iff (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (rule : RewriteRule) (term result : Pattern) :
    result ∈ applyRuleAt relEnv lang ambient rule term ↔
      ∃ spec captured assignment,
        rule.bindings = some spec ∧
        admittedFor rule spec = true ∧
        captured ∈ matchRuleAt rule spec ambient term ∧
        assignment ∈ completeAssignments relEnv lang ambient rule spec captured ∧
        reduct? rule spec ambient assignment = some result :=
  mem_applyRuleWithAt_iff Substitution.instantiateBVar relEnv lang ambient rule term result

/-- Apply the scoped rules of an authored language at the root of an explicit
ambient context, retaining rule and match multiplicities. Rules without a
binding declaration do not enter this scoped route. -/
def rewriteStepAt (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (term : Pattern) : List Pattern :=
  lang.rewrites.flatMap fun rule => applyRuleAt relEnv lang ambient rule term

theorem mem_rewriteStepAt_iff (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (term result : Pattern) :
    result ∈ rewriteStepAt relEnv lang ambient term ↔
      ∃ rule ∈ lang.rewrites, result ∈ applyRuleAt relEnv lang ambient rule term := by
  exact List.mem_flatMap

end Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
