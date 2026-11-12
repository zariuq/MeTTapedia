import Mettapedia.Machines.TIsa.Control
import Mettapedia.Machines.TIsa.RegisterProfile

/-!
# Canonical Boolean branching with linear control tokens

A branch keeps its condition and replaces only the current control token.
Its choice is checked against the scalar Boolean interpretation; a malformed
condition has neither branch. All other data cells remain untouched.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Control

open Cells CellEffects

universe u
variable {Key : Type u} [DecidableEq Key]

structure Branch (Key : Type u) where
  activation : Nat
  point : Word
  condition : Key
  yes : Word
  no : Word
  deriving DecidableEq, Repr

def Branch.target? (branch : Branch Key) (condition : Word) : Option Word :=
  (RegisterProfile.truth condition).map fun choose => if choose then branch.yes else branch.no

def Branch.recipe (branch : Branch Key) : Recipe (Location Key) where
  inputs := [.inl branch.activation, .inr branch.condition]
  outputs := [.inl branch.activation]
  guard := fun inputs outputs => match inputs, outputs with
    | [point, condition], [next] => point == branch.point && branch.target? condition == some next
    | _, _ => false

omit [DecidableEq Key] in
theorem Branch.guard_iff (branch : Branch Key) (before after : Location Key → Word) :
    branch.recipe.guard (branch.recipe.inputs.map before) (branch.recipe.outputs.map after) = true ↔
      before (.inl branch.activation) = branch.point ∧
      branch.target? (before (.inr branch.condition)) = some (after (.inl branch.activation)) := by
  simp [recipe]

theorem Branch.overwrite_eq (branch : Branch Key) (before after : Location Key → Word) :
    overwrite branch.recipe.writes before after =
      Function.update before (.inl branch.activation) (after (.inl branch.activation)) := by
  funext key
  by_cases same : key = .inl branch.activation <;> simp [overwrite, Recipe.writes, recipe, same]

theorem Branch.realized (branch : Branch Key) (keys : Finset (Location Key))
    (before : Location Key → Word) (next : Word)
    (included : branch.recipe.support ⊆ keys)
    (current : before (.inl branch.activation) = branch.point)
    (chosen : branch.target? (before (.inr branch.condition)) = some next) :
    ∃ invocation : Invocation branch.recipe,
      CellEffects.system.Enables (encode keys before) invocation ∧
      CellEffects.system.fire (encode keys before) invocation =
        encode keys (Function.update before (.inl branch.activation) next) := by
  let after := Function.update before (.inl branch.activation) next
  have guarded : branch.recipe.guard (branch.recipe.inputs.map before) (branch.recipe.outputs.map after) = true := by
    apply (branch.guard_iff before after).mpr
    simpa [after] using And.intro current chosen
  obtain ⟨invocation, enabled, endpoint⟩ := effect_realized branch.recipe keys before after included guarded
  refine ⟨invocation, enabled, ?_⟩
  simpa [branch.overwrite_eq, after] using endpoint

omit [DecidableEq Key] in
theorem Branch.target?_iff (branch : Branch Key) (condition next : Word) :
    branch.target? condition = some next ↔
      (condition = 0 ∧ next = branch.no) ∨ (condition = 1 ∧ next = branch.yes) := by
  by_cases zero : condition = 0#64
  · subst condition
    simp [target?, RegisterProfile.truth, eq_comm]
  · by_cases one : condition = 1#64
    · subst condition
      simp [target?, RegisterProfile.truth, eq_comm]
    · simp [target?, RegisterProfile.truth, zero, one]

theorem Branch.preserves_data (branch : Branch Key) (before after : Location Key → Word) (key : Key) :
    overwrite branch.recipe.writes before after (.inr key) = before (.inr key) := by
  simp [overwrite, Recipe.writes, recipe]

namespace BranchControls

private def branch : Branch Nat := ⟨0, 4, 1, 5, 6⟩

example : branch.recipe.guard [4, 0] [6] = true := by decide
example : branch.recipe.guard [4, 1] [5] = true := by decide
example : branch.recipe.guard [4, 2] [5] = false := by decide
example : branch.recipe.guard [4, 0] [5] = false := by decide
example : branch.recipe.guard [3, 0] [6] = false := by decide

end BranchControls

end Mettapedia.Machines.TIsa.Control
