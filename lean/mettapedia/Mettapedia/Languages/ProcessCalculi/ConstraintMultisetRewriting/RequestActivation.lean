import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ABTDataChecks
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.RequestSteps

/-!
# Request templates and their data conditions activate into ordinary steps

One source recipe retains the request, premise templates, conclusion and
Boolean data computation together. Activation instantiates those templates
and records that exact computation as a closed ABT equality check. A proof
object is not interpreted by this construction.

The matching-receipt embedding preserves the physical take/read/output
choices. It concerns data-only request conditions, not arbitrary observed
regions or event-trace equality. General schema admission, publication rights
and logical soundness of the source recipe remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestActivation

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {V Head P : Type}

structure Recipe (V Head P : Type) where
  request : P
  premises : List P
  conclusion : P
  dataCondition : Subst V (Term Head) → Bool

def Recipe.matchingRule (recipe : Recipe V Head P) : GuardedMultisetRewriting.Rule V (Term Head) P :=
  GuardedMultisetRewriting.requestRule recipe.request recipe.premises recipe.conclusion recipe.dataCondition

/-- The finite supplied columns do not bind identities outside the declared
input prefix. The name universe itself is still unbounded. -/
def boundedAssignment (arity : Nat) (values : List (Term Head)) : Subst Nat (Term Head) :=
  fun index => if index < arity then values[index]? else none

theorem boundedAssignment_binds (layer : TermLayer Nat (Term Head) P)
    (recipe : Recipe Nat Head P) (arity : Nat) (values : List (Term Head))
    (contains : ∀ index < arity, index ∈ layer.vars recipe.request) :
    GuardedMultisetRewriting.BindsOnlyGathers layer recipe.matchingRule (boundedAssignment arity values) := by
  intro index outside
  by_cases inside : index < arity
  · exact False.elim (outside recipe.request (by simp [Recipe.matchingRule, GuardedMultisetRewriting.requestRule])
      (contains index inside))
  · exact if_neg inside

def fromValues (falseHead trueHead : Head) (request : Term Head) (premises : List (Term Head))
    (conclusion : Term Head) (decision : Bool) : RuleInstance (Term Head) :=
  ⟨[request], premises, [], [ABTDataChecks.check falseHead trueHead decision], [conclusion]⟩

def activate (layer : TermLayer V (Term Head) P) (falseHead trueHead : Head)
    (recipe : Recipe V Head P) (assignment : Subst V (Term Head)) : Option (RuleInstance (Term Head)) := do
  let request ← layer.inst assignment recipe.request
  let premises ← instTemplate layer assignment recipe.premises
  let conclusion ← layer.inst assignment recipe.conclusion
  return fromValues falseHead trueHead request premises conclusion (recipe.dataCondition assignment)

theorem activate_iff (layer : TermLayer V (Term Head) P) (falseHead trueHead : Head)
    (recipe : Recipe V Head P) (assignment : Subst V (Term Head)) (rule : RuleInstance (Term Head)) :
    activate layer falseHead trueHead recipe assignment = some rule ↔
      ∃ request premises conclusion,
        layer.inst assignment recipe.request = some request ∧
        instTemplate layer assignment recipe.premises = some premises ∧
        layer.inst assignment recipe.conclusion = some conclusion ∧
        rule = fromValues falseHead trueHead request premises conclusion (recipe.dataCondition assignment) := by
  cases request : layer.inst assignment recipe.request with
  | none => simp [activate, request]
  | some requestValue =>
      cases premises : instTemplate layer assignment recipe.premises with
      | none => simp [activate, request, premises]
      | some premiseValues =>
          cases conclusion : layer.inst assignment recipe.conclusion with
          | none => simp [activate, request, premises, conclusion]
          | some conclusionValue => simp [activate, request, premises, conclusion, eq_comm]

def physicalSelection {O : Type*} (receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head)) : Selection O :=
  ⟨receipt.takes, receipt.reads, receipt.outputs⟩

theorem condition_of_valid {O : Type*} [DecidableEq O]
    (layer : TermLayer V (Term Head) P) (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead)
    (width : Nat) (recipe : Recipe V Head P) (assignment : Subst V (Term Head))
    {rule : RuleInstance (Term Head)} {picked : Selection O} {label : O → Term Head}
    {before : Configuration (Term Head) O}
    (computed : activate layer falseHead trueHead recipe assignment = some rule)
    (valid : picked.Valid (ABTProtectedParameters.action width) label rule before) :
    recipe.dataCondition assignment = true := by
  obtain ⟨request, premises, conclusion, _, _, _, rfl⟩ :=
    (activate_iff layer falseHead trueHead recipe assignment rule).mp computed
  obtain ⟨candidate, models⟩ := valid.consistent
  have accepted := valid.checks (ABTDataChecks.check falseHead trueHead (recipe.dataCondition assignment))
    (by simp [fromValues]) candidate models
  exact (ABTDataChecks.holds_iff falseHead trueHead distinct width _ candidate label before.present).mp accepted

theorem false_condition_refuses {O : Type*} [DecidableEq O]
    (layer : TermLayer V (Term Head) P) (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead)
    (width : Nat) (recipe : Recipe V Head P) (assignment : Subst V (Term Head))
    {rule : RuleInstance (Term Head)} (picked : Selection O) (label : O → Term Head)
    (before : Configuration (Term Head) O)
    (computed : activate layer falseHead trueHead recipe assignment = some rule)
    (refused : recipe.dataCondition assignment = false) :
    ¬picked.Valid (ABTProtectedParameters.action width) label rule before := by
  intro valid
  have accepted := condition_of_valid layer falseHead trueHead distinct width recipe assignment computed valid
  rw [refused] at accepted
  cases accepted

theorem instTemplate_of_matches (layer : TermLayer V (Term Head) P) (structural : layer.E = Eq)
    (assignment : Subst V (Term Head)) {patterns : List P} {values : List (Term Head)}
    (matched : List.Forall₂ (layer.Solves assignment) patterns values) :
    instTemplate layer assignment patterns = some values := by
  induction matched with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨value, computed, equal⟩ := head
      rw [structural] at equal
      subst value
      simp only [instTemplate] at ih
      simp [instTemplate, computed, ih]

theorem self_equations {T : Type*} {S : Type*} {O : Type*}
    (action : SubstitutionAction T S) (assignment : S) (label : O → T) (picked : List O) :
    action.Models assignment (Selection.equations label (picked.map label) picked) := by
  apply (Selection.models_equations_iff action assignment label (by simp)).mpr
  apply List.forall₂_map_left_iff.mpr
  exact List.forall₂_same.mpr fun _ _ => action.equivalence.refl _

/-- A source receipt activates through the same instantiation/data functions
and gives an ordinary constraint step with the same physical selections.
The source check is data-only; it never reads the store as an input. -/
theorem step_of_matching_receipt {O : Type*} [DecidableEq O]
    (layer : TermLayer V (Term Head) P) (structural : layer.E = Eq)
    (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead) (width : Nat)
    (recipe : Recipe V Head P) (label : O → Term Head) (before : Configuration (Term Head) O)
    (receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head))
    (valid : receipt.ValidAt layer recipe.matchingRule label before.present)
    (background : (ABTProtectedParameters.action width).Consistent before.equations) :
    ∃ rule, activate layer falseHead trueHead recipe receipt.assignment = some rule ∧
      Step (ABTProtectedParameters.action width) label rule before
        ((physicalSelection receipt).result label rule before) := by
  have takeInstances := instTemplate_of_matches layer structural receipt.assignment valid.takesMatch
  have readInstances := instTemplate_of_matches layer structural receipt.assignment valid.readsMatch
  change instTemplate layer receipt.assignment [recipe.request] = some (receipt.takes.map label) at takeInstances
  change instTemplate layer receipt.assignment recipe.premises = some (receipt.reads.map label) at readInstances
  cases request : layer.inst receipt.assignment recipe.request with
  | none => simp [instTemplate, request] at takeInstances
  | some requestValue =>
      have takeValues : [requestValue] = receipt.takes.map label := by
        simpa [instTemplate, request] using takeInstances
      have outputInstances := valid.makes
      change instTemplate layer receipt.assignment [recipe.conclusion] = some (receipt.outputs.map label) at outputInstances
      cases conclusion : layer.inst receipt.assignment recipe.conclusion with
      | none => simp [instTemplate, conclusion] at outputInstances
      | some conclusionValue =>
          have outputValues : [conclusionValue] = receipt.outputs.map label := by
            simpa [instTemplate, conclusion] using outputInstances
          let rule := fromValues falseHead trueHead requestValue (receipt.reads.map label) conclusionValue
            (recipe.dataCondition receipt.assignment)
          refine ⟨rule, ?_, physicalSelection receipt, ?_, rfl⟩
          · simp [activate, request, readInstances, conclusion, rule]
          · have checked : recipe.dataCondition receipt.assignment = true :=
              valid.checks_hold ⟨recipe.request, fun assignment _ => recipe.dataCondition assignment = true⟩
                (by simp [Recipe.matchingRule, GuardedMultisetRewriting.requestRule])
            refine ⟨valid.uniqueTakes, valid.uniqueOutputs, ?_, by simp [rule, fromValues, physicalSelection],
              outputValues.symm,
              ⟨valid.takesPresent, valid.readsPresent, valid.apart, valid.fresh, by simp [Selection.commit]⟩,
              ?_, ?_⟩
            · simpa [rule, fromValues, physicalSelection, Recipe.matchingRule,
                GuardedMultisetRewriting.requestRule] using valid.takesMatch.length_eq
            · obtain ⟨candidate, models⟩ := background
              refine ⟨candidate, ?_⟩
              change (ABTProtectedParameters.action width).Models candidate
                (before.equations ++ Selection.equations label [requestValue] receipt.takes ++
                  Selection.equations label (receipt.reads.map label) receipt.reads ++ [])
              simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true]
              have takeSolved : (ABTProtectedParameters.action width).Models candidate
                  (Selection.equations label [requestValue] receipt.takes) := by
                rw [takeValues]
                exact self_equations (ABTProtectedParameters.action width) candidate label receipt.takes
              exact ⟨⟨models, takeSolved⟩,
                self_equations (ABTProtectedParameters.action width) candidate label receipt.reads⟩
            · intro query member candidate _
              have same : query = ABTDataChecks.check falseHead trueHead
                  (recipe.dataCondition receipt.assignment) := by simpa [rule, fromValues] using member
              subst query
              exact (ABTDataChecks.holds_iff falseHead trueHead distinct width _ candidate label before.present).mpr checked

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestActivation
