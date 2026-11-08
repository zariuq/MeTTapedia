import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStep
import Mathlib.Data.List.OfFn

/-!
# The already-active-row profile of contextual occurrence activation

When the rule and stored values contain only shared captures, computed views
are independent of their use ports. The positive activation step is then
exactly the existing ordinary step in the common extended frame. Existing
equations, labels and rule positions are all transported into that frame.

This comparison forgets the private scope ledger, whose updated value is
still required by the activation step. It does not assert that arbitrary
endomorphic solutions descend into a smaller declaration family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveStepProfile

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualActivatedStep

universe u
variable {S : Signature} {Local Shared : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def rawRule {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S captures) Γ sort)) :=
  rule.map (instantiate (ContextualSelectionViews.capturedSource locals captures))

def targetRule {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S captures) Γ sort)) :=
  rule.map (instantiate (ContextualSelectionViews.capturedTarget locals captures))

def sharedRows {Γ : Ctx S} {sort : S.Srt} (label : O → Term (signature S captures) Γ sort) :
    O → ContextualStoredRows.Row locals captures Γ sort :=
  fun occurrence => .shared (label occurrence)

def targetLabel {Γ : Ctx S} {sort : S.Srt} (label : O → Term (signature S captures) Γ sort) :
    O → Term (signature S (target locals captures)) Γ sort :=
  fun occurrence => instantiate (ContextualSelectionViews.capturedTarget locals captures) (label occurrence)

private theorem check_map_twice {T U V : Type*} (first : T → U) (second : U → V) (check : Check T) :
    (check.map first).map second = check.map (second ∘ first) := by
  cases check <;> rfl

private theorem rule_map_twice {T U V : Type*} (first : T → U) (second : U → V) (rule : RuleInstance T) :
    (rule.map first).map second = rule.map (second ∘ first) := by
  cases rule
  simp only [RuleInstance.map, List.map_map, Function.comp_def, check_map_twice]

theorem freshened_captured_rule (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S captures) Γ sort)) :
    ContextualFreshening.ruleAt locals captures scope (rawRule locals captures rule) =
      targetRule locals captures rule := by
  change ((rule.map (instantiate (ContextualSelectionViews.capturedSource locals captures))).map
    (ContextualFreshening.termAt locals captures scope)) = _
  rw [rule_map_twice]
  have same : (fun value : Term (signature S captures) Γ sort =>
      ContextualFreshening.termAt locals captures scope
        (instantiate (ContextualSelectionViews.capturedSource locals captures) value)) =
      fun value : Term (signature S captures) Γ sort =>
        instantiate (ContextualSelectionViews.capturedTarget locals captures) value := by
    funext value
    exact (ContextualStoredRows.viewAt_eq_freshening locals captures scope (.shared value)).symm
  exact congrArg (fun f : Term (signature S captures) Γ sort →
    Term (signature S (target locals captures)) Γ sort => rule.map f) same

theorem prepared_rule_eq (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S captures) Γ sort))
    (label : O → Term (signature S captures) Γ sort) :
    (prepared locals captures occupied selection (rawRule locals captures rule)
      (sharedRows locals captures label)).rule = targetRule locals captures rule :=
  freshened_captured_rule locals captures _ rule

private theorem ofFn_get_map {T U : Type*} (values : List T) (f : T → U) :
    List.ofFn (fun position : Fin values.length => f (values.get position)) = values.map f := by
  change List.ofFn (f ∘ values.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem taken_values_eq (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S captures) Γ sort))
    (label : O → Term (signature S captures) Γ sort) :
    List.ofFn (prepared locals captures occupied selection (rawRule locals captures rule)
      (sharedRows locals captures label)).taken = selection.taken.map (targetLabel locals captures label) := by
  calc
    _ = List.ofFn (fun position : Fin selection.taken.length =>
        targetLabel locals captures label (selection.taken.get position)) := by
      congr 1
      funext position
      rw [prepared_taken_view]
      rfl
    _ = _ := ofFn_get_map _ _

theorem read_values_eq (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S captures) Γ sort))
    (label : O → Term (signature S captures) Γ sort) :
    List.ofFn (prepared locals captures occupied selection (rawRule locals captures rule)
      (sharedRows locals captures label)).read = selection.read.map (targetLabel locals captures label) := by
  calc
    _ = List.ofFn (fun position : Fin selection.read.length =>
        targetLabel locals captures label (selection.read.get position)) := by
      congr 1
      funext position
      rw [prepared_read_view]
      rfl
    _ = _ := ofFn_get_map _ _

theorem problem_eq (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S captures) Γ sort))
    (label : O → Term (signature S captures) Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    problem locals captures occupied selection (rawRule locals captures rule) (sharedRows locals captures label) before =
      selection.problem (targetLabel locals captures label) (targetRule locals captures rule)
        (frame locals captures before) := by
  simp only [problem, prepared_rule_eq, taken_values_eq, read_values_eq, useEquations,
    Selection.problem, Selection.equations, List.zipWith_map_right, id]

theorem result_eq [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S captures) Γ sort))
    (label : O → Term (signature S captures) Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    result locals captures occupied selection (rawRule locals captures rule) (sharedRows locals captures label) before =
      selection.result (targetLabel locals captures label) (targetRule locals captures rule)
        (frame locals captures before) := by
  apply congrArg₂ Configuration.mk
  · exact problem_eq locals captures occupied selection rule label before
  · rfl

theorem resultRows_eq [DecidableEq O] (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (label : O → Term (signature S captures) Γ sort) :
    resultRows locals captures selection (targetLabel locals captures label) (sharedRows locals captures label) =
      sharedRows locals (target locals captures) (targetLabel locals captures label) := by
  funext occurrence
  simp only [resultRows, sharedRows, ContextualStoredRows.Row.map, targetLabel]
  split <;> rfl

theorem valid_iff [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (ground : ∀ result, Term (signature S (target locals captures)) [] result)
    (rule : RuleInstance (Term (signature S captures) Γ sort)) (noChecks : rule.checks = [])
    (label : O → Term (signature S captures) Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    Valid locals captures occupied selection (rawRule locals captures rule) (sharedRows locals captures label)
      before (targetLabel locals captures label) ↔
      selection.Valid (ContextualFamilies.action (target locals captures) Γ sort)
        (targetLabel locals captures label) (targetRule locals captures rule) (frame locals captures before) := by
  constructor
  · intro valid
    refine ⟨valid.take_distinct, valid.output_distinct, ?_, ?_, ?_, valid.occurrences, ?_, ?_⟩
    · simpa only [rawRule, targetRule, RuleInstance.map, List.length_map] using valid.take_length
    · simpa only [rawRule, targetRule, RuleInstance.map, List.length_map] using valid.read_length
    · simpa only [prepared_rule_eq] using valid.outputs
    · have model := (ContextualFrameUnifier.solvable_iff_consistent ground _).mp valid.solvable
      simpa only [problem_eq] using model
    · intro check member
      simp only [targetRule, RuleInstance.map, noChecks, List.map_nil, List.not_mem_nil] at member
  · intro valid
    refine ⟨?_, valid.take_distinct, valid.output_distinct, ?_, ?_, ?_, valid.occurrences, ?_⟩
    · simp only [rawRule, RuleInstance.map, noChecks, List.map_nil]
    · simpa only [rawRule, targetRule, RuleInstance.map, List.length_map] using valid.take_length
    · simpa only [rawRule, targetRule, RuleInstance.map, List.length_map] using valid.read_length
    · simpa only [prepared_rule_eq] using valid.outputs
    · apply ContextualFrameUnifier.solvable_of_consistent
      simpa only [problem_eq] using valid.consistent

/-- With all source rows and rule variables already shared, the positive
activation step, observed without its private ledger and in a frame
with ground terms for every sort, is the existing ordinary step on the explicitly transported common frame. -/
theorem step_iff [DecidableEq O] (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (ground : ∀ result, Term (signature S (target locals captures)) [] result)
    (rule : RuleInstance (Term (signature S captures) Γ sort)) (noChecks : rule.checks = [])
    (label : O → Term (signature S captures) Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (after : Configuration (Term (signature S (target locals captures)) Γ sort) O) :
    (∃ ledger, ContextualActivatedStep.Step locals captures occupied (rawRule locals captures rule)
      (sharedRows locals captures label) before (targetLabel locals captures label) after
      (sharedRows locals (target locals captures) (targetLabel locals captures label)) ledger) ↔
      ConstraintMultisetRewriting.Step (ContextualFamilies.action (target locals captures) Γ sort)
        (targetLabel locals captures label) (targetRule locals captures rule) (frame locals captures before) after := by
  constructor
  · rintro ⟨ledger, selection, valid, rfl, _, _⟩
    exact ⟨selection, (valid_iff locals captures occupied selection ground rule noChecks label before).mp valid,
      result_eq locals captures occupied selection rule label before⟩
  · rintro ⟨selection, valid, rfl⟩
    refine ⟨ContextualActivationScopes.after occupied selection, selection,
      (valid_iff locals captures occupied selection ground rule noChecks label before).mpr valid, ?_, ?_, rfl⟩
    · exact (result_eq locals captures occupied selection rule label before).symm
    · exact (resultRows_eq locals captures selection label).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveStepProfile
