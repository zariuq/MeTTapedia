import Mettapedia.Logic.ModalMuCalculus
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Complete inspection of admitted finite modal unfoldings

The existing fixed-point-free formula syntax is inspected independently of
its propositional satisfaction relation. Each supplied successor list is
traversed completely. Repeated successors remain repeated work occurrences,
even though their relation support is unchanged.

The admission proof rules out fixed-point binders in this finite procedure.
No unsupported binder receives an invented Boolean meaning. Actual unfolding
formulas can use this procedure after their admission has been earned.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.Inspection

universe u v

structure SuccessorPresentation (State : Type u) (Action : Type v) where
  successors : State → Action → List State

variable {State : Type u} {Action : Type v}

def SuccessorPresentation.toLTS (presentation : SuccessorPresentation State Action) :
    LTS State Action where
  trans source action target := target ∈ presentation.successors source action

abbrev BooleanEnv (State : Type u) (n : Nat) := Fin n → State → Bool

def BooleanEnv.toEnv {n : Nat} (environment : BooleanEnv State n) : Env State n :=
  fun index => {state | environment index state = true}

/-- Eager inspection retains the cost of every child of both Boolean and
modal connectives, including repeated supplied successor occurrences. -/
def inspect (presentation : SuccessorPresentation State Action) {n : Nat} :
    (formula : Formula Action n) → formula.isHML = true → BooleanEnv State n →
      State → Bool × Nat
  | .tt, _, _, _ => (true, 1)
  | .ff, _, _, _ => (false, 1)
  | .var index, _, environment, state => (environment index state, 1)
  | .neg body, admitted, environment, state =>
      let checked := inspect presentation body admitted environment state
      (!checked.1, 1 + checked.2)
  | .conj first second, admitted, environment, state =>
      let before := inspect presentation first (Bool.and_eq_true_iff.mp admitted).1 environment state
      let after := inspect presentation second (Bool.and_eq_true_iff.mp admitted).2 environment state
      (before.1 && after.1, 1 + before.2 + after.2)
  | .disj first second, admitted, environment, state =>
      let before := inspect presentation first (Bool.and_eq_true_iff.mp admitted).1 environment state
      let after := inspect presentation second (Bool.and_eq_true_iff.mp admitted).2 environment state
      (before.1 || after.1, 1 + before.2 + after.2)
  | .diamond action body, admitted, environment, state =>
      let checked := (presentation.successors state action).map
        (fun successor => inspect presentation body admitted environment successor)
      (checked.any Prod.fst, 1 + (checked.map Prod.snd).sum)
  | .box action body, admitted, environment, state =>
      let checked := (presentation.successors state action).map
        (fun successor => inspect presentation body admitted environment successor)
      (checked.all Prod.fst, 1 + (checked.map Prod.snd).sum)
  | .mu _, admitted, _, _ => False.elim (Bool.false_ne_true admitted)
  | .nu _, admitted, _, _ => False.elim (Bool.false_ne_true admitted)

theorem inspect_truth {n : Nat} (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) :
    (inspect presentation formula admitted environment state).1 = true ↔
      satisfies presentation.toLTS environment.toEnv formula state := by
  induction formula generalizing state with
  | tt => simp only [inspect, satisfies]
  | ff => simp only [inspect, satisfies, Bool.false_eq_true]
  | var index => rfl
  | neg body inductionHypothesis =>
      change (!(inspect presentation body admitted environment state).1) = true ↔
        ¬ satisfies presentation.toLTS environment.toEnv body state
      rw [← inductionHypothesis admitted environment state]
      cases (inspect presentation body admitted environment state).1 <;> decide
  | conj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      change ((inspect presentation first parts.1 environment state).1 &&
        (inspect presentation second parts.2 environment state).1) = true ↔ _ ∧ _
      rw [Bool.and_eq_true_iff, firstHypothesis parts.1 environment state,
        secondHypothesis parts.2 environment state]
  | disj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      change ((inspect presentation first parts.1 environment state).1 ||
        (inspect presentation second parts.2 environment state).1) = true ↔ _ ∨ _
      rw [Bool.or_eq_true_iff, firstHypothesis parts.1 environment state,
        secondHypothesis parts.2 environment state]
  | diamond action body inductionHypothesis =>
      change ((presentation.successors state action).map
        (fun successor => inspect presentation body admitted environment successor)).any Prod.fst = true ↔
        ∃ successor, successor ∈ presentation.successors state action ∧
          satisfies presentation.toLTS environment.toEnv body successor
      simp only [List.any_map, List.any_eq_true]
      constructor
      · rintro ⟨successor, member, checked⟩
        exact ⟨successor, member, (inductionHypothesis admitted environment successor).1 checked⟩
      · rintro ⟨successor, member, satisfied⟩
        exact ⟨successor, member, (inductionHypothesis admitted environment successor).2 satisfied⟩
  | box action body inductionHypothesis =>
      change ((presentation.successors state action).map
        (fun successor => inspect presentation body admitted environment successor)).all Prod.fst = true ↔
        ∀ successor, successor ∈ presentation.successors state action →
          satisfies presentation.toLTS environment.toEnv body successor
      simp only [List.all_map, List.all_eq_true]
      constructor
      · intro checked successor member
        exact (inductionHypothesis admitted environment successor).1 (checked successor member)
      · intro satisfied successor member
        exact (inductionHypothesis admitted environment successor).2 (satisfied successor member)
  | mu body => exact False.elim (Bool.false_ne_true admitted)
  | nu body => exact False.elim (Bool.false_ne_true admitted)

theorem inspect_falsehood {n : Nat} (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) :
    (inspect presentation formula admitted environment state).1 = false ↔
      ¬ satisfies presentation.toLTS environment.toEnv formula state := by
  rw [← inspect_truth presentation formula admitted environment state]
  cases (inspect presentation formula admitted environment state).1 <;> decide

theorem inspection_positive {n : Nat} (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) :
    0 < (inspect presentation formula admitted environment state).2 := by
  cases formula
  all_goals try exact False.elim (Bool.false_ne_true admitted)
  all_goals simp only [inspect]
  all_goals omega

end Mettapedia.Logic.ModalMuCalculus.Inspection
