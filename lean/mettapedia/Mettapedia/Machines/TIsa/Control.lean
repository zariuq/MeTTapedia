import Mettapedia.Machines.TIsa.CellEffects

/-!
# Control tokens and scalar calls as finite transform profiles

Control is an ordinary linear cell, distinct from data cells. A row consumes
the current control token and destination, keeps its shared inputs, and makes
the successor token and value. The finite source row list supplies the actual
resource system; there is no separate program interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Control

open Cells

universe u
variable {Key : Type u} [DecidableEq Key]

abbrev Location (Key : Type u) := Sum Nat Key

structure Row (Key : Type u) where
  activation : Nat
  point : Word
  next : Word
  action : Action Key
  deriving DecidableEq, Repr

def Row.recipe (row : Row Key) : CellEffects.Recipe (Location Key) where
  inputs := .inl row.activation :: row.action.inputs.map Sum.inr
  outputs := [.inl row.activation, .inr row.action.destination]
  guard := fun inputs outputs => match inputs, outputs with
    | pc :: arguments, [next, result] =>
        pc == row.point && next == row.next && row.action.scalar.evaluate arguments == some result
    | _, _ => false

omit [DecidableEq Key] in
theorem Row.guard_iff (row : Row Key) (before after : Location Key → Word) :
    row.recipe.guard (row.recipe.inputs.map before) (row.recipe.outputs.map after) = true ↔
      before (.inl row.activation) = row.point ∧
      after (.inl row.activation) = row.next ∧
      row.action.scalar.evaluate (row.action.inputs.map (fun key => before (.inr key))) =
        some (after (.inr row.action.destination)) := by
  simp only [recipe, List.map_cons, List.map_nil, List.map_map,
    Bool.and_eq_true, beq_iff_eq, Function.comp_def, and_assoc]

/-- The successor is a direct readback of the two produced cells. -/
def Row.nextValues (row : Row Key) (before : Location Key → Word) (result : Word) : Location Key → Word :=
  Function.update (Function.update before (.inl row.activation) row.next) (.inr row.action.destination) result

theorem Row.overwrite_eq_nextValues (row : Row Key) (before after : Location Key → Word)
    (next : after (.inl row.activation) = row.next)
    (result : Word) (value : after (.inr row.action.destination) = result) :
    CellEffects.overwrite row.recipe.writes before after = row.nextValues before result := by
  funext location
  cases location with
  | inl activation =>
      by_cases same : activation = row.activation
      · subst activation
        simp [CellEffects.overwrite, CellEffects.Recipe.writes, recipe, nextValues, next]
      · simp [CellEffects.overwrite, CellEffects.Recipe.writes, recipe, nextValues, same]
  | inr key =>
      by_cases same : key = row.action.destination
      · subst key
        simp [CellEffects.overwrite, CellEffects.Recipe.writes, recipe, nextValues, value]
      · simp [CellEffects.overwrite, CellEffects.Recipe.writes, recipe, nextValues, same]

theorem Row.nextValues_guard (row : Row Key) (before : Location Key → Word) (result : Word)
    (pc : before (.inl row.activation) = row.point)
    (computed : row.action.scalar.evaluate (row.action.inputs.map (fun key => before (.inr key))) =
      some result) :
    row.recipe.guard (row.recipe.inputs.map before)
      (row.recipe.outputs.map (row.nextValues before result)) = true := by
  apply (row.guard_iff before _).mpr
  simpa [nextValues] using And.intro pc computed

/-- A scalar source step with its continuation is one actual resource firing. -/
theorem Row.realized (row : Row Key) (keys : Finset (Location Key))
    (before : Location Key → Word) (result : Word) (included : row.recipe.support ⊆ keys)
    (pc : before (.inl row.activation) = row.point)
    (computed : row.action.scalar.evaluate (row.action.inputs.map (fun key => before (.inr key))) =
      some result) :
    ∃ invocation : CellEffects.Invocation row.recipe,
      CellEffects.system.Enables (encode keys before) invocation ∧
      CellEffects.system.fire (encode keys before) invocation = encode keys (row.nextValues before result) := by
  obtain ⟨invocation, enabled, same⟩ := CellEffects.effect_realized row.recipe keys before
    (row.nextValues before result) included (row.nextValues_guard before result pc computed)
  refine ⟨invocation, enabled, ?_⟩
  rw [same, row.overwrite_eq_nextValues before (row.nextValues before result)
    (by simp [nextValues]) result (by simp [nextValues])]

def program (rows : List (Row Key)) := CellEffects.profile (rows.map Row.recipe)

/-- A hosted program can only take one of its actual source rows. -/
theorem program_rewrite_iff (rows : List (Row Key)) (keys : Finset (Location Key))
    (before : Location Key → Word) (after : Multiset (Cell (Location Key))) :
    (program rows).theory.rewrites (encode keys before) after ↔
      ∃ row ∈ rows, ∃ result : Word,
        row.recipe.support ⊆ keys ∧ before (.inl row.activation) = row.point ∧
        row.action.scalar.evaluate (row.action.inputs.map (fun key => before (.inr key))) = some result ∧
        after = encode keys (row.nextValues before result) := by
  rw [program, CellEffects.profile_rewrite_iff]
  constructor
  · rintro ⟨recipe, member, written, included, guarded, endpoint⟩
    obtain ⟨row, source, rfl⟩ := List.mem_map.mp member
    obtain ⟨pc, next, computed⟩ := (row.guard_iff before written).mp guarded
    exact ⟨row, source, written (.inr row.action.destination), included, pc, computed,
      by rw [endpoint, row.overwrite_eq_nextValues before written next _ rfl]⟩
  · rintro ⟨row, source, result, included, pc, computed, rfl⟩
    refine ⟨row.recipe, List.mem_map.mpr ⟨row, source, rfl⟩, row.nextValues before result,
      included, row.nextValues_guard before result pc computed, ?_⟩
    rw [row.overwrite_eq_nextValues before (row.nextValues before result)
      (by simp [Row.nextValues]) result (by simp [Row.nextValues])]

namespace Controls

private def row : Row Nat := ⟨0, 3, 4, ⟨.binary .add, [0, 0], 0⟩⟩
private def before : Location Nat → Word
  | .inl _ => 3
  | .inr _ => 7

example : row.recipe.guard (row.recipe.inputs.map before)
    (row.recipe.outputs.map (row.nextValues before 14)) = true := by decide

example : row.recipe.guard [2, 7, 7] [4, 14] = false := by decide

example : row.recipe.guard [3, 7, 7] [5, 14] = false := by decide

example : row.recipe.guard [3, 7, 7] [4, 15] = false := by decide

end Controls

end Mettapedia.Machines.TIsa.Control
