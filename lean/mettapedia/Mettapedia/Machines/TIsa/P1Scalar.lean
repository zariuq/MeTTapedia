import Mettapedia.Machines.TIsa.P1Source
import Mettapedia.Machines.TIsa.Typing
import Mettapedia.Machines.TIsa.Continuation

/-!
# p1 scalar instructions as finite transform effects

Instruction data comes from the actual p1 source vocabulary. This module
supplies only its pure word algebra and register recipes. BOOL operands are
checked; narrow shifts and comparisons operate at 32 bits before extension.
Memory operations need their byte/capability recipes and are not scalar calls.

Successful recipes take/replace the destination and share repeated reads.
Invalid-input recipes preserve every data cell and transfer the existing
control token to the supplied invalid-input handler. The handler's status
writes, static admission and concrete native templates have separate proofs.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.P1Scalar
open P1Source Cells CellEffects

def narrow : TypeTag → Bool
  | .u32z | .i32s => true | _ => false

def normalize : TypeTag → Word → Word
  | .u32z, value => ScalarType.u32z.normalize value
  | .i32s, value => ScalarType.i32s.normalize value
  | _, value => value

def boolInputs (ty : TypeTag) (values : List Word) : Bool :=
  ty != .boolean || values.all (fun value => decide (value.toNat ≤ 1))

def compareWords (condition : Comparison) (ty : TypeTag) (left right : Word) : Word :=
  booleanWord (if narrow ty then condition.evaluate (low32 left) (low32 right)
    else condition.evaluate left right)

def shiftWord (operation : Shift) (ty : TypeTag) (value : Word) (amount : Nat) : Option Word :=
  if amount < (if narrow ty then 32 else 64) then
    some (if narrow ty then normalize ty ((operation.evaluate (low32 value) amount).zeroExtend 64)
      else operation.evaluate value amount)
  else none

def evaluate : Instr → List Word → Option Word
  | .immediate ty _ value, [] => some (normalize ty value)
  | .move ty _ _, [value] => if boolInputs ty [value] then some (normalize ty value) else none
  | .binary operation ty _ _ _, [left, right] =>
      if boolInputs ty [left, right] then some (normalize ty (operation.evaluate left right)) else none
  | .shift operation ty _ _ amount, [value] => shiftWord operation ty value amount
  | .extract ty _ _ low width, [value] =>
      if 0 < width ∧ low + width ≤ 64 then
        some (normalize ty (BitVec.ofNat 64 ((value.toNat / 2 ^ low) % 2 ^ width))) else none
  | .compare condition ty _ _ (.register _), [left, right] => some (compareWords condition ty left right)
  | .compare condition ty _ _ (.immediate right), [left] => some (compareWords condition ty left right)
  | .select ty _ _ _ _, [condition, yes, no] =>
      if condition.toNat ≤ 1 ∧ boolInputs ty [yes, no] then
        some (normalize ty (if condition = 1 then yes else no)) else none
  | _, _ => none

def supported : Instr → Bool
  | .address .. | .load .. | .loadFrame .. | .store .. => false
  | _ => true

def recipe (instruction : Instr) (destination : Reg) : Recipe Reg where
  inputs := instruction.reads
  outputs := [destination]
  guard := fun inputs outputs => match outputs with
    | [result] => evaluate instruction inputs == some result
    | _ => false

def lower? (instruction : Instr) : Option (Recipe Reg) :=
  if supported instruction then (instruction.destination?).map (recipe instruction) else none

theorem guard_iff (instruction : Instr) (destination : Reg) (before after : Reg → Word) :
    (recipe instruction destination).guard ((recipe instruction destination).inputs.map before)
      ((recipe instruction destination).outputs.map after) = true ↔
      evaluate instruction (instruction.reads.map before) = some (after destination) := by
  simp [recipe]

theorem overwrite_eq (instruction : Instr) (destination : Reg) (before after : Reg → Word) :
    overwrite (recipe instruction destination).writes before after =
      Function.update before destination (after destination) := by
  funext register
  by_cases same : register = destination
  · subst register
    simp [overwrite, Recipe.writes, recipe]
  · simp [overwrite, Recipe.writes, recipe, same]

theorem rewrite_iff (instruction : Instr) (destination : Reg) (keys : Finset Reg)
    (before : Reg → Word) (world : Multiset (Cell Reg)) :
    (profile [recipe instruction destination]).theory.rewrites (encode keys before) world ↔
      ∃ result, (recipe instruction destination).support ⊆ keys ∧
        evaluate instruction (instruction.reads.map before) = some result ∧
        world = encode keys (Function.update before destination result) := by
  rw [profile_rewrite_iff]
  constructor
  · rintro ⟨effect, member, after, included, guarded, endpoint⟩
    have same : effect = recipe instruction destination := by simpa using member
    subst effect
    exact ⟨after destination, included, (guard_iff instruction destination before after).mp guarded,
      by rw [endpoint, overwrite_eq]⟩
  · rintro ⟨result, included, computed, endpoint⟩
    refine ⟨recipe instruction destination, by simp, Function.update before destination result, included, ?_, ?_⟩
    · apply (guard_iff instruction destination before _).mpr
      simpa using computed
    · simpa only [overwrite_eq, Function.update_self] using endpoint

def edge (activation : Nat) (point next : Word) (instruction : Instr) (destination : Reg) :
    Control.Edge Reg := ⟨activation, point, next, recipe instruction destination⟩

theorem edge_guard_iff (activation : Nat) (point next : Word) (instruction : Instr) (destination : Reg)
    (before after : Control.Location Reg → Word) :
    (edge activation point next instruction destination).recipe.guard
      ((edge activation point next instruction destination).recipe.inputs.map before)
      ((edge activation point next instruction destination).recipe.outputs.map after) = true ↔
      before (.inl activation) = point ∧ after (.inl activation) = next ∧
        evaluate instruction (instruction.reads.map (fun register => before (.inr register))) =
          some (after (.inr destination)) := by
  simp only [edge, Control.Edge.guard_iff, guard_iff]

theorem lower?_eq_some_iff (instruction : Instr) (effect : Recipe Reg) :
    lower? instruction = some effect ↔
      supported instruction = true ∧ ∃ destination,
        instruction.destination? = some destination ∧ effect = recipe instruction destination := by
  by_cases supports : supported instruction = true
  · simp only [lower?, supports, if_true, true_and]
    cases destination : instruction.destination? with
    | none => simp
    | some destination => simp [eq_comm]
  · simp [lower?, supports]

def invalidRecipe (instruction : Instr) : Recipe Reg where
  inputs := instruction.reads
  outputs := []
  guard := fun inputs outputs => outputs.isEmpty && (evaluate instruction inputs).isNone

def invalidEdge (activation : Nat) (point invalid : Word) (instruction : Instr) : Control.Edge Reg :=
  ⟨activation, point, invalid, invalidRecipe instruction⟩

theorem invalid_guard_iff (activation : Nat) (point invalid : Word) (instruction : Instr)
    (before after : Control.Location Reg → Word) :
    (invalidEdge activation point invalid instruction).recipe.guard
      ((invalidEdge activation point invalid instruction).recipe.inputs.map before)
      ((invalidEdge activation point invalid instruction).recipe.outputs.map after) = true ↔
      before (.inl activation) = point ∧ after (.inl activation) = invalid ∧
        evaluate instruction (instruction.reads.map (fun register => before (.inr register))) = none := by
  simp [invalidEdge, Control.Edge.guard_iff, invalidRecipe]

theorem invalid_preserves_data (activation : Nat) (point invalid : Word) (instruction : Instr)
    (before after : Control.Location Reg → Word) (register : Reg) :
    (invalidEdge activation point invalid instruction).finish before after (.inr register) = before (.inr register) := by
  simp [Control.Edge.finish, invalidEdge, invalidRecipe, overwrite, Recipe.writes]

theorem invalid_finish_eq (activation : Nat) (point invalid : Word) (instruction : Instr)
    (before after : Control.Location Reg → Word) :
    (invalidEdge activation point invalid instruction).finish before after =
      Function.update before (.inl activation) invalid := by
  exact (invalidEdge activation point invalid instruction).finish_of_no_outputs rfl before after

theorem invalid_realized (activation : Nat) (point invalid : Word) (instruction : Instr)
    (keys : Finset (Control.Location Reg)) (before : Control.Location Reg → Word)
    (included : (invalidEdge activation point invalid instruction).recipe.support ⊆ keys)
    (atPoint : before (.inl activation) = point)
    (failed : evaluate instruction
      (instruction.reads.map (fun register => before (.inr register))) = none) :
    ∃ invocation : Invocation (invalidEdge activation point invalid instruction).recipe,
      CellEffects.system.Enables (encode keys before) invocation ∧
      CellEffects.system.fire (encode keys before) invocation =
        encode keys (Function.update before (.inl activation) invalid) := by
  let after := Function.update before (.inl activation) invalid
  obtain ⟨invocation, enabled, endpoint⟩ :=
    (invalidEdge activation point invalid instruction).realized keys before after included
      ((invalid_guard_iff activation point invalid instruction before after).mpr
        ⟨atPoint, by simp [after], failed⟩)
  refine ⟨invocation, enabled, endpoint.trans ?_⟩
  exact congrArg (encode keys) (invalid_finish_eq activation point invalid instruction before after)

/-- Reflection includes invalid inputs; a failed scalar does not silently suspend. -/
theorem invalid_rewrite_iff (activation : Nat) (point invalid : Word) (instruction : Instr)
    (keys : Finset (Control.Location Reg)) (before : Control.Location Reg → Word)
    (world : Multiset (Cell (Control.Location Reg))) :
    (Control.edgeProgram [invalidEdge activation point invalid instruction]).theory.rewrites
      (encode keys before) world ↔
      (invalidEdge activation point invalid instruction).recipe.support ⊆ keys ∧
      before (.inl activation) = point ∧
      evaluate instruction (instruction.reads.map (fun register => before (.inr register))) = none ∧
      world = encode keys (Function.update before (.inl activation) invalid) := by
  rw [Control.edgeProgram_rewrite_iff]
  constructor
  · rintro ⟨edge, member, after, included, atPoint, _, failed, endpoint⟩
    have same : edge = invalidEdge activation point invalid instruction := by simpa using member
    subst edge
    refine ⟨included, atPoint, ?_, ?_⟩
    · simpa [invalidEdge, invalidRecipe] using failed
    · simpa only [invalid_finish_eq] using endpoint
  · rintro ⟨included, atPoint, failed, endpoint⟩
    let after := Function.update before (.inl activation) invalid
    refine ⟨invalidEdge activation point invalid instruction, by simp, after,
      included, atPoint, ?_, ?_, ?_⟩
    · simp [invalidEdge, after]
    · simpa [invalidEdge, invalidRecipe] using failed
    · simpa only [invalid_finish_eq] using endpoint

namespace Controls

theorem mov_boolean_rejects_two : evaluate (.move .boolean 1 2) [2] = none := by decide

theorem shift_32_signed : evaluate (.shift .rightSigned .u32z 1 2 1) [0x80000000] = some 0xc0000000 := by decide

theorem shift_32_signed_extended :
    evaluate (.shift .rightSigned .i32s 1 2 1) [0x80000000] = some 0xffffffffc0000000 := by decide

theorem compare_32_signed :
    evaluate (.compare .lessSigned .i32s 1 2 (.immediate 0)) [0x80000000] = some 1 := by decide

theorem compare_32_unsigned :
    evaluate (.compare .lessUnsigned .u32z 1 2 (.immediate 0)) [0x80000000] = some 0 := by decide

theorem duplicate_read_is_one_cell :
    (recipe (.binary .add .u64 3 1 1) 3).reads = {1} := by decide

theorem destination_alias_is_taken_once :
    (recipe (.binary .add .u64 1 1 1) 1).reads = ∅ ∧
      (recipe (.binary .add .u64 1 1 1) 1).writes = {1} := by decide

theorem alias_fires :
    (profile [recipe (.binary .add .u64 1 1 1) 1]).theory.rewrites
      (encode {1} (fun _ => 7)) (encode {1} (fun _ => 14)) := by
  apply (rewrite_iff _ _ _ _ _).mpr
  refine ⟨14, by decide, by decide, ?_⟩
  apply encode_congr
  intro register member
  have same : register = (1 : Reg) := by simpa using member
  subst register
  simp

theorem memory_needs_its_resource_lowering :
    (lower? (.load .u64 .word64 0 1 2 0)).isNone = true := by decide

private def invalidBooleanState : Control.Location Reg → Word
  | .inl _ => 11
  | .inr register => if register = 2 then 2 else 77

theorem invalid_boolean_fires :
    (Control.edgeProgram [invalidEdge 0 11 99 (.move .boolean 1 2)]).theory.rewrites
      (encode {.inl 0, .inr 1, .inr 2} invalidBooleanState)
      (encode {.inl 0, .inr 1, .inr 2} (Function.update invalidBooleanState (.inl 0) 99)) := by
  apply (invalid_rewrite_iff _ _ _ _ _ _ _).mpr
  exact ⟨by decide, rfl, by decide, rfl⟩

theorem invalid_boolean_keeps_destination :
    (invalidEdge 0 11 99 (.move .boolean 1 2)).finish invalidBooleanState invalidBooleanState (.inr 1) = 77 := by
  rw [invalid_preserves_data]
  decide

end Controls
end Mettapedia.Machines.TIsa.P1Scalar
