import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuleGrammar
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Reindex

/-! # Authored rule payloads interpreted by the actual occurrence step

The binding-tree action and occurrence labels are explicit interpretation
parameters of this profile. Decoded rules and selections become candidates
of the existing first-order interface instance, with its real resource,
equation and check obligations. The profile has no extra predicate queries.
Parsing supplies data; it neither assumes nor manufactures admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads.Execution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
open Interface

abbrev State := Configuration Term Nat
abbrev Candidate := RuleInstance Term × Selection Nat

def step (label : Nat → Term) :=
  (AnnotatedRuns.firstOrder (BindingTrees.action (Head := Head)) label).toStep.reindex
    (fun (candidate : Candidate) => ⟨candidate.1, [], candidate.2⟩)

theorem admits_iff (label : Nat → Term) (rule : RuleInstance Term) (selection : Selection Nat)
    (before : State) : (step label).Admits (s := before) (rule, selection) ↔
      selection.Valid BindingTrees.action label rule before :=
  PredicateQueryAdmission.valid_empty_iff BindingTrees.action label rule before selection

theorem result_eq (label : Nat → Term) (rule : RuleInstance Term) (selection : Selection Nat)
    (before : State) (permitted : (step label).Admits (s := before) (rule, selection)) :
    (step label).result (rule, selection) permitted = selection.result label rule before := rfl

def Executes (label : Nat → Term) (ruleData selectionData beforeData afterData : Pattern) : Prop :=
  ∃ (rule : RuleInstance Term) (selection : Selection Nat) (before after : State),
    readRule ruleData = some rule ∧ readSelection selectionData = some selection ∧
    readConfiguration beforeData = some before ∧ readConfiguration afterData = some after ∧
    (step label).Admits (s := before) (rule, selection) ∧
    selection.result label rule before = after

/-- Both directions refer to the existing calculus, including its admission
conditions. Successful decoding alone is insufficient. -/
theorem encoded_execution_iff (label : Nat → Term) (rule : RuleInstance Term)
    (selection : Selection Nat) (before after : State) :
    Executes label (rulePattern rule) (selectionPattern selection)
      (configurationPattern before) (configurationPattern after) ↔
      selection.Valid BindingTrees.action label rule before ∧ selection.result label rule before = after := by
  simp only [Executes, readRule_pattern, readSelection_pattern, readConfiguration_pattern,
    Option.some.injEq, admits_iff]
  constructor
  · rintro ⟨_, _, _, _, rfl, rfl, rfl, rfl, valid, result⟩
    exact ⟨valid, result⟩
  · intro execution
    exact ⟨rule, selection, before, after, rfl, rfl, rfl, rfl, execution⟩

theorem encoded_execution_iff_interface (label : Nat → Term) (rule : RuleInstance Term)
    (selection : Selection Nat) (before after : State) :
    Executes label (rulePattern rule) (selectionPattern selection)
      (configurationPattern before) (configurationPattern after) ↔
      ∃ permitted : (step label).Admits (s := before) (rule, selection),
        (step label).result (rule, selection) permitted = after := by
  rw [encoded_execution_iff]
  constructor
  · rintro ⟨valid, result⟩
    exact ⟨(admits_iff label rule selection before).mpr valid, result⟩
  · rintro ⟨permitted, result⟩
    exact ⟨(admits_iff label rule selection before).mp permitted, result⟩

theorem printed_execution_iff (label : Nat → Term) (rule : RuleInstance Term)
    (selection : Selection Nat) (before after : State) :
    Executes label ((syntaxAlgebra rules).evaluate (ruleRoute rule)).tree
      ((syntaxAlgebra rules).evaluate (selectionRoute selection)).tree
      ((syntaxAlgebra rules).evaluate (configurationRoute before)).tree
      ((syntaxAlgebra rules).evaluate (configurationRoute after)).tree ↔
      selection.Valid BindingTrees.action label rule before ∧ selection.result label rule before = after := by
  rw [ruleRoute_tree, selectionRoute_tree, configurationRoute_tree,
    configurationRoute_tree, encoded_execution_iff]

namespace Controls

def label (index : Nat) : Term := .node (.name (index + 7)) .nil
def before : State := ⟨[], {0}⟩
def selection : Selection Nat := ⟨[0], [], [1]⟩
def rule : RuleInstance Term := ⟨[label 0], [], [], [], [label 1]⟩
def after : State := selection.result label rule before

theorem valid : selection.Valid BindingTrees.action label rule before where
  take_distinct := by simp [selection]
  output_distinct := by simp [selection]
  take_length := rfl
  read_length := rfl
  outputs := rfl
  occurrences := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [selection, before, Selection.commit]
    · simp [selection, Selection.commit]
    · simp [selection, Selection.commit]
    · simp [selection, before, Selection.commit]
    · intro query member
      simp [selection, Selection.commit] at member
  consistent := by
    refine ⟨Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.idx, ?_⟩
    intro equation member
    have same : equation = (label 0, label 0) := by
      simpa [Selection.problem, Selection.equations, selection, rule, before] using member
    subst equation
    rfl
  checks := by simp [rule]

theorem encoded_linear_firing : Executes label (rulePattern rule) (selectionPattern selection)
    (configurationPattern before) (configurationPattern after) :=
  (encoded_execution_iff label rule selection before after).mpr ⟨valid, rfl⟩

theorem occurrence_effect_is_nontrivial : before.present = {0} ∧ after.present = {1} := by
  simp [before, after, Selection.result, selection, Selection.commit,
    MeTTaCalculus.OccurrenceCommits.fire]

def refusedRule : RuleInstance Term := { rule with checks := [.absent (label 0)] }

theorem refused_rule_prepares : (step label).Prepares (s := before) (refusedRule, selection) := by
  change (step label).Prepares (s := before) (rule, selection)
  exact (step label).prepares ((admits_iff label rule selection before).mpr valid)

theorem refused_rule_not_admitted : ¬ (step label).Admits (s := before) (refusedRule, selection) := by
  intro permitted
  have accepted := (admits_iff label refusedRule selection before).mp permitted
  obtain ⟨substitution, solved⟩ := accepted.consistent
  have absent := accepted.checks (.absent (label 0)) (List.mem_singleton_self _) substitution solved
  exact absent 0 (by simp [before]) rfl

theorem no_encoded_guard_bypass (target : State) :
    ¬ Executes label (rulePattern refusedRule) (selectionPattern selection)
      (configurationPattern before) (configurationPattern target) := by
  intro execution
  obtain ⟨permitted, _⟩ := (encoded_execution_iff_interface label refusedRule selection before target).mp execution
  exact refused_rule_not_admitted permitted

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads.Execution
