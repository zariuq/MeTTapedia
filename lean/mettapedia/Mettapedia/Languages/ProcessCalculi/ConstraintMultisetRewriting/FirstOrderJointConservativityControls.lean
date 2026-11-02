import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtensionControls

/-!
# Preserving each marginal does not preserve their joint possibilities

Starting from no equations, the actual tell x = y preserves every possible
value of x and every possible value of y separately: set the other name to
the protected value. It removes the old joint possibility x = A, y = B.
Caller interfaces containing both names therefore require one joint extension
witness; independent singleton permissions do not suffice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtension.JointControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A zero)
open FirstOrderConservativeExtension.Controls (picked label beforeOpen)

def equate : RuleInstance (Term signature) := ⟨[], [], [(.var 0, .var 1)], [], []⟩
def after : Configuration (Term signature) Nat := picked.result label equate beforeOpen
def both : Set Nat := {0, 1}
def split : Subst signature := (Subst.single (σ := signature) 1 (.const 1)).comp zero

theorem equate_valid : picked.Valid A label equate beforeOpen := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨Subst.single 0 (.var 1), ?_⟩
    intro equation member
    have same : equation = (Term.var (σ := signature) 0, .var 1) := by
      simpa [Selection.problem, Selection.equations, beforeOpen, picked, equate] using member
    subst equation
    rfl
  · simp [equate]

theorem actual_equating_step : Step A label equate beforeOpen after :=
  ⟨picked, equate_valid, rfl⟩

theorem equated_in_every_new_model (assignment : Subst signature)
    (model : A.Models assignment after.equations) : assignment 0 = assignment 1 :=
  model (.var 0, .var 1) (by
    simp [after, Selection.result, Selection.problem, Selection.equations, beforeOpen, picked, equate])

theorem preserves_x_separately :
    ConservativeOn ({0} : Set Nat) beforeOpen.equations after.equations := by
  intro old _
  let extended : Subst signature := fun name => if name = 1 then old 0 else old name
  refine ⟨extended, ?_, ?_⟩
  · intro equation member
    have same : equation = (Term.var (σ := signature) 0, .var 1) := by
      simpa [after, Selection.result, Selection.problem, Selection.equations,
        beforeOpen, picked, equate] using member
    subst equation
    change extended 0 = extended 1
    simp [extended]
  · intro name inside
    have atZero : name = 0 := by simpa using inside
    subst name
    simp [extended]

theorem preserves_y_separately :
    ConservativeOn ({1} : Set Nat) beforeOpen.equations after.equations := by
  intro old _
  let extended : Subst signature := fun name => if name = 0 then old 1 else old name
  refine ⟨extended, ?_, ?_⟩
  · intro equation member
    have same : equation = (Term.var (σ := signature) 0, .var 1) := by
      simpa [after, Selection.result, Selection.problem, Selection.equations,
        beforeOpen, picked, equate] using member
    subst equation
    change extended 0 = extended 1
    simp [extended]
  · intro name inside
    have atOne : name = 1 := by simpa using inside
    subst name
    simp [extended]

theorem every_x_value_is_preserved (value : Term signature) :
    (∃ assignment, A.Models assignment after.equations ∧ assignment 0 = value) ↔
      ∃ assignment, A.Models assignment beforeOpen.equations ∧ assignment 0 = value := by
  apply possible_value_iff preserves_x_separately actual_equating_step.refines (.var 0) value
  intro name member
  simpa [Term.freeVars] using member

theorem every_y_value_is_preserved (value : Term signature) :
    (∃ assignment, A.Models assignment after.equations ∧ assignment 1 = value) ↔
      ∃ assignment, A.Models assignment beforeOpen.equations ∧ assignment 1 = value := by
  apply possible_value_iff preserves_y_separately actual_equating_step.refines (.var 1) value
  intro name member
  simpa [Term.freeVars] using member

theorem unequal_old_pair_is_possible :
    ∃ assignment, A.Models assignment beforeOpen.equations ∧
      assignment 0 = Term.const (σ := signature) 0 ∧ assignment 1 = Term.const (σ := signature) 1 :=
  ⟨split, A.models_nil split, rfl, rfl⟩

theorem unequal_old_pair_is_no_longer_possible :
    ¬ ∃ assignment, A.Models assignment after.equations ∧
      assignment 0 = Term.const (σ := signature) 0 ∧ assignment 1 = Term.const (σ := signature) 1 := by
  rintro ⟨assignment, model, atZero, atOne⟩
  have same := equated_in_every_new_model assignment model
  rw [atZero, atOne] at same
  cases same

theorem joint_component_is_not_preserved :
    ¬ ConservativeOn both beforeOpen.equations after.equations := by
  intro preserves
  obtain ⟨extended, model, agree⟩ := preserves split (A.models_nil split)
  exact unequal_old_pair_is_no_longer_possible
    ⟨extended, model, agree 0 (by simp [both]), agree 1 (by simp [both])⟩

theorem marginal_preservation_does_not_imply_joint_preservation :
    Step A label equate beforeOpen after ∧
      ConservativeOn ({0} : Set Nat) beforeOpen.equations after.equations ∧
      ConservativeOn ({1} : Set Nat) beforeOpen.equations after.equations ∧
      ¬ ConservativeOn both beforeOpen.equations after.equations :=
  ⟨actual_equating_step, preserves_x_separately, preserves_y_separately,
    joint_component_is_not_preserved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtension.JointControls
