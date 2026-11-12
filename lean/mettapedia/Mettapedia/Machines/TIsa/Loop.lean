import Mettapedia.Machines.TIsa.Branch

/-!
# Bounded-loop resource templates

The bound register is read at entry and immutable throughout the body. Thus
its resource is already the captured bound; no extra snapshot register is
introduced. Entry and latch are ordinary finite cell recipes. The latch's
natural-number rank decreases without a machine-word wraparound.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Control

open Cells CellEffects

universe u
variable {Key : Type u} [DecidableEq Key]

structure Loop (Key : Type u) where
  activation : Nat
  entryPoint : Word
  headerPoint : Word
  latchPoint : Word
  bodyPoint : Word
  exitPoint : Word
  index : Key
  bound : Key
  maximum : Nat
  deriving DecidableEq, Repr

def Loop.check (loop : Loop Key) : Bool :=
  decide (loop.index ≠ loop.bound ∧ 0 < loop.maximum ∧ loop.maximum < 2 ^ 32)

def Loop.entry (loop : Loop Key) : Recipe (Location Key) where
  inputs := [.inl loop.activation, .inr loop.bound]
  outputs := [.inl loop.activation, .inr loop.index]
  guard := fun inputs outputs => match inputs, outputs with
    | [point, bound], [next, index] =>
        loop.check && point == loop.entryPoint && next == loop.headerPoint && index == 0 &&
          decide (bound.toNat ≤ loop.maximum)
    | _, _ => false

def Loop.latch (loop : Loop Key) : Recipe (Location Key) where
  inputs := [.inl loop.activation, .inr loop.index, .inr loop.bound]
  outputs := [.inl loop.activation, .inr loop.index]
  guard := fun inputs outputs => match inputs, outputs with
    | [point, index, bound], [next, following] =>
        loop.check && point == loop.latchPoint && next == loop.headerPoint &&
          decide (index.toNat < bound.toNat) && decide (bound.toNat ≤ loop.maximum) && following == index + 1
    | _, _ => false

def Loop.headerTarget (loop : Loop Key) (index bound : Word) : Word :=
  if index.toNat < bound.toNat then loop.bodyPoint else loop.exitPoint

def Loop.header (loop : Loop Key) : Recipe (Location Key) where
  inputs := [.inl loop.activation, .inr loop.index, .inr loop.bound]
  outputs := [.inl loop.activation]
  guard := fun inputs outputs => match inputs, outputs with
    | [point, index, bound], [next] =>
        loop.check && point == loop.headerPoint && decide (index.toNat ≤ bound.toNat) &&
          decide (bound.toNat ≤ loop.maximum) && next == loop.headerTarget index bound
    | _, _ => false

theorem Loop.entry_guard_iff (loop : Loop Key) (before after : Location Key → Word) :
    loop.entry.guard (loop.entry.inputs.map before) (loop.entry.outputs.map after) = true ↔
      loop.check = true ∧ before (.inl loop.activation) = loop.entryPoint ∧
      after (.inl loop.activation) = loop.headerPoint ∧ after (.inr loop.index) = 0 ∧
      (before (.inr loop.bound)).toNat ≤ loop.maximum := by
  simp [entry, Bool.and_eq_true, and_assoc]

theorem Loop.latch_guard_iff (loop : Loop Key) (before after : Location Key → Word) :
    loop.latch.guard (loop.latch.inputs.map before) (loop.latch.outputs.map after) = true ↔
      loop.check = true ∧ before (.inl loop.activation) = loop.latchPoint ∧
      after (.inl loop.activation) = loop.headerPoint ∧
      (before (.inr loop.index)).toNat < (before (.inr loop.bound)).toNat ∧
      (before (.inr loop.bound)).toNat ≤ loop.maximum ∧
      after (.inr loop.index) = before (.inr loop.index) + 1 := by
  simp [latch, Bool.and_eq_true, and_assoc]

theorem Loop.header_guard_iff (loop : Loop Key) (before after : Location Key → Word) :
    loop.header.guard (loop.header.inputs.map before) (loop.header.outputs.map after) = true ↔
      loop.check = true ∧ before (.inl loop.activation) = loop.headerPoint ∧
      (before (.inr loop.index)).toNat ≤ (before (.inr loop.bound)).toNat ∧
      (before (.inr loop.bound)).toNat ≤ loop.maximum ∧
      after (.inl loop.activation) = loop.headerTarget (before (.inr loop.index)) (before (.inr loop.bound)) := by
  simp [header, Bool.and_eq_true, and_assoc]

theorem Loop.bound_not_written (loop : Loop Key) (checked : loop.check = true) :
    .inr loop.bound ∉ loop.entry.writes ∧ .inr loop.bound ∉ loop.latch.writes ∧
      .inr loop.bound ∉ loop.header.writes := by
  have distinct : loop.index ≠ loop.bound := (of_decide_eq_true checked).1
  simp [entry, latch, header, Recipe.writes, Ne.symm distinct]

theorem preserved_outside_writes (recipe : Recipe (Location Key)) (before after : Location Key → Word)
    (key : Location Key) (outside : key ∉ recipe.writes) :
    overwrite recipe.writes before after key = before key := if_neg outside

theorem Loop.body_preserves_control_data (loop : Loop Key) (body : Recipe (Location Key))
    (before after : Location Key → Word)
    (indexReadOnly : .inr loop.index ∉ body.writes) (boundReadOnly : .inr loop.bound ∉ body.writes) :
    overwrite body.writes before after (.inr loop.index) = before (.inr loop.index) ∧
      overwrite body.writes before after (.inr loop.bound) = before (.inr loop.bound) :=
  ⟨if_neg indexReadOnly, if_neg boundReadOnly⟩

theorem counter_increment_no_wrap (index bound : Word) (less : index.toNat < bound.toNat) :
    (index + 1).toNat = index.toNat + 1 := by
  have within : index.toNat + 1 < 2 ^ 64 := by have := bound.isLt; omega
  simpa [BitVec.toNat_add] using within

theorem Loop.latch_decreases (loop : Loop Key) (before after : Location Key → Word)
    (guarded : loop.latch.guard (loop.latch.inputs.map before) (loop.latch.outputs.map after) = true) :
    let next := overwrite loop.latch.writes before after
    (next (.inr loop.bound)).toNat - (next (.inr loop.index)).toNat + 1 =
      (before (.inr loop.bound)).toNat - (before (.inr loop.index)).toNat := by
  obtain ⟨checked, _, _, less, _, increment⟩ := (loop.latch_guard_iff before after).mp guarded
  have retained : .inr loop.bound ∉ loop.latch.writes := (loop.bound_not_written checked).2.1
  have replaced : .inr loop.index ∈ loop.latch.writes := by simp [latch, Recipe.writes]
  simp only [overwrite, if_neg retained, if_pos replaced, increment, counter_increment_no_wrap _ _ less]
  omega

theorem Loop.latch_preserves_bound (loop : Loop Key) (before after : Location Key → Word)
    (checked : loop.check = true) :
    overwrite loop.latch.writes before after (.inr loop.bound) = before (.inr loop.bound) :=
  if_neg (loop.bound_not_written checked).2.1

def Loop.rank (loop : Loop Key) (values : Location Key → Word) : Nat :=
  (values (.inr loop.bound)).toNat - (values (.inr loop.index)).toNat

/-- A readback step of the actual guarded latch recipe. -/
def Loop.LatchStep (loop : Loop Key) (before next : Location Key → Word) : Prop :=
  ∃ after : Location Key → Word,
    loop.latch.guard (loop.latch.inputs.map before) (loop.latch.outputs.map after) = true ∧
    next = overwrite loop.latch.writes before after

theorem Loop.latchStep_decreases (loop : Loop Key) (before next : Location Key → Word)
    (step : loop.LatchStep before next) : loop.rank next < loop.rank before := by
  obtain ⟨after, guarded, rfl⟩ := step
  have decreased := loop.latch_decreases before after guarded
  change loop.rank (overwrite loop.latch.writes before after) + 1 = loop.rank before at decreased
  omega

/-- The bounded counter cannot admit an infinite chain of latch firings. -/
theorem Loop.latch_wellFounded (loop : Loop Key) :
    WellFounded (fun next before => loop.LatchStep before next) := by
  apply (measure loop.rank).wf.mono
  intro next before step
  exact loop.latchStep_decreases before next step

namespace LoopControls

private def loop : Loop Nat := ⟨0, 1, 2, 3, 4, 5, 0, 1, 10⟩

example : loop.entry.guard [1, 10] [2, 0] = true := by decide
example : loop.entry.guard [1, 11] [2, 0] = false := by decide
example : loop.header.guard [2, 0, 0] [5] = true := by decide
example : loop.header.guard [2, 9, 10] [4] = true := by decide
example : loop.latch.guard [3, 9, 10] [2, 10] = true := by decide
example : loop.latch.guard [3, 10, 10] [2, 11] = false := by decide
example : ({ loop with bound := 0 }).check = false := by decide

end LoopControls

end Mettapedia.Machines.TIsa.Control
