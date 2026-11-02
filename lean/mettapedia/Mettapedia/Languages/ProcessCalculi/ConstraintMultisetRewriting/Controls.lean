import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

/-!
# Two-sided bindings, shared reads and unresolved checks

These controls use the existing first-order term syntax. A selected call
binds a variable occurring in a surviving frame; equal-valued occurrences
remain distinct resources. An unresolved absence check is neither proved nor
refuted merely because its current argument is unbound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

abbrev signature : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Unit
  functionArity _ := 1

abbrev A := FirstOrder.action signature

def f (term : Term signature) : Term signature := .app () (fun _ => term)

def label : Nat → Term signature
  | 0 => f (.var 0)
  | 1 => .var 0
  | 2 => .const 1
  | 3 => .const 0
  | 4 => .var 0
  | _ => .const 2

def initial : Configuration (Term signature) Nat := ⟨[], {0, 1}⟩

def callRule : RuleInstance (Term signature) :=
  ⟨[f (.const 0)], [], [], [], [.const 1]⟩

def callSelection : Selection Nat := ⟨[0], [], [2]⟩

def zero : Subst signature := Subst.single 0 (.const 0)
def one : Subst signature := Subst.single 0 (.const 1)

theorem call_valid : callSelection.Valid A label callRule initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨zero, ?_⟩
    intro equation member
    have same : equation = (f (.const 0), f (.var 0)) := by
      simpa [Selection.problem, Selection.equations, initial, callRule, callSelection, label]
        using member
    subst equation
    rfl
  · simp [callRule]

theorem call_steps : Step A label callRule initial (callSelection.result label callRule initial) :=
  ⟨callSelection, call_valid, rfl⟩

/-- Binding the selected call also binds the caller's surviving variable. -/
theorem caller_binding_reaches_frame (σ : Subst signature)
    (solved : A.Models σ (callSelection.result label callRule initial).equations) :
    σ.applyTerm (label 1) = .const 0 := by
  have same := solved (f (.const 0), f (.var 0)) (by
    simp [Selection.result, Selection.problem, Selection.equations, initial, callRule, callSelection,
      label])
  change f (.const 0) = f (σ 0) at same
  have children : (fun _ : Fin 1 => Term.const (σ := signature) 0) = (fun _ => σ 0) := by
    exact eq_of_heq (Term.app.inj same).2
  exact (congr_fun children 0).symm

theorem caller_frame_survives :
    1 ∈ (callSelection.result label callRule initial).present := by decide

theorem caller_value_cannot_stay_arbitrary :
    ¬ A.Models one (callSelection.result label callRule initial).equations := by
  intro solved
  have impossible := caller_binding_reaches_frame one solved
  change (Term.const (σ := signature) 1) = .const 0 at impossible
  cases impossible

theorem call_has_principal_answer : ∃ answer,
    A.Principal (callSelection.problem label callRule initial) answer := by
  obtain ⟨answer, accepted⟩ :=
    (FirstOrder.accepted_iff_consistent (signature := signature) _).mpr call_valid.consistent
  exact ⟨answer, FirstOrder.accepted_principal (signature := signature) _ _ accepted⟩

theorem variable_against_variable_has_principal_answer :
    ∃ answer, A.Principal [(Term.var 0, Term.var 1)] answer := by
  have consistent : A.Consistent [(Term.var 0, Term.var 1)] := by
    refine ⟨Subst.single 0 (.var 1), ?_⟩
    intro equation member
    have same : equation = (Term.var (σ := signature) 0, Term.var (σ := signature) 1) := by
      simpa using member
    subst equation
    rfl
  obtain ⟨answer, accepted⟩ :=
    (FirstOrder.accepted_iff_consistent (signature := signature) _).mpr consistent
  exact ⟨answer, FirstOrder.accepted_principal (signature := signature) _ _ accepted⟩

def readsRule : RuleInstance (Term signature) :=
  ⟨[], [.var 0, .var 0], [], [], []⟩

def sharedRead : Selection Nat := ⟨[], [1, 1], []⟩
def singletonStore : Configuration (Term signature) Nat := ⟨[], {1}⟩

theorem two_reads_share_one_occurrence : sharedRead.Valid A label readsRule singletonStore := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨Subst.id signature, ?_⟩
    intro equation member
    have same : equation = (Term.var (σ := signature) 0, Term.var (σ := signature) 0) := by
      simpa [Selection.problem, Selection.equations, singletonStore, readsRule, sharedRead, label]
        using member
    subst equation
    rfl
  · simp [readsRule]

def twoTakes : RuleInstance (Term signature) := ⟨[.var 0, .var 0], [], [], [], []⟩
def duplicateTake : Selection Nat := ⟨[1, 1], [], []⟩
def distinctTake : Selection Nat := ⟨[1, 4], [], []⟩
def duplicateValuedStore : Configuration (Term signature) Nat := ⟨[], {1, 4}⟩

theorem cannot_consume_one_occurrence_twice :
    ¬ duplicateTake.Valid A label twoTakes singletonStore := by
  intro valid
  have impossible := valid.take_distinct
  simp [duplicateTake] at impossible

theorem equal_values_allow_distinct_consumption :
    distinctTake.Valid A label twoTakes duplicateValuedStore := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨Subst.id signature, ?_⟩
    intro equation member
    have same : equation = (Term.var (σ := signature) 0, Term.var (σ := signature) 0) := by
      simpa [Selection.problem, Selection.equations, duplicateValuedStore, twoTakes, distinctTake,
        label] using member
    subst equation
    rfl
  · simp [twoTakes]

/-- No binding is made by an ask; the unbound argument leaves two possibilities. -/
theorem open_absence_is_not_entailed :
    ¬ A.Entails [] (fun σ => (Check.absent (.const 0)).Holds A σ label {1}) := by
  intro entailed
  have absent := entailed zero (A.models_nil zero)
  exact absent 1 (by simp) rfl

theorem open_presence_is_not_entailed :
    ¬ A.Entails [] (fun σ => ¬(Check.absent (.const 0)).Holds A σ label {1}) := by
  intro entailed
  apply entailed one (A.models_nil one)
  intro o member equal
  have selected : o = 1 := by simpa using member
  subst o
  change (Term.const (σ := signature) 0) = .const 1 at equal
  cases equal

theorem occurs_cycle_refused :
    unifyTotal [(Term.var (σ := signature) 0, f (.var 0))] = none := by
  simp [unifyTotal, f, Term.occursIn]

theorem finite_tree_profile_has_no_cycle_solution :
    ¬ A.Consistent [(Term.var 0, f (.var 0))] :=
  (FirstOrder.refused_iff_inconsistent (signature := signature) _).mp occurs_cycle_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls
