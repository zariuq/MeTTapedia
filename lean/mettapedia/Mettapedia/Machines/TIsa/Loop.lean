import Mettapedia.Machines.TIsa.Branch

/-!
# Bounded-loop resource templates

The bound register is read at entry and immutable throughout the body. Thus
its resource is already the captured bound; no extra snapshot register is
introduced. Entry and latch are ordinary finite cell recipes. The latch's
natural-number rank decreases without a machine-word wraparound.
Admitted header and latch updates are realized by actual resource firings;
the fired latch retains the same strict rank decrease.
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

def Loop.entryValues (loop : Loop Key) (before : Location Key → Word) : Location Key → Word :=
  Function.update (Function.update before (.inl loop.activation) loop.headerPoint) (.inr loop.index) 0

theorem Loop.entryValues_guard (loop : Loop Key) (before : Location Key → Word)
    (checked : loop.check = true) (current : before (.inl loop.activation) = loop.entryPoint)
    (bounded : (before (.inr loop.bound)).toNat ≤ loop.maximum) :
    loop.entry.guard (loop.entry.inputs.map before) (loop.entry.outputs.map (loop.entryValues before)) = true := by
  apply (loop.entry_guard_iff before _).mpr
  exact ⟨checked,current,by simp [entryValues],by simp [entryValues],bounded⟩

theorem Loop.entry_overwrite (loop : Loop Key) (before : Location Key → Word) :
    overwrite loop.entry.writes before (loop.entryValues before) = loop.entryValues before := by
  funext location
  cases location with
  | inl activation =>
    by_cases same : activation = loop.activation
    · subst activation
      simp [overwrite,Recipe.writes,entry,entryValues]
    · simp [overwrite,Recipe.writes,entry,entryValues,same]
  | inr key =>
    by_cases same : key = loop.index
    · subst key
      simp [overwrite,Recipe.writes,entry,entryValues]
    · simp [overwrite,Recipe.writes,entry,entryValues,same]

theorem Loop.entry_realized (loop : Loop Key) (keys : Finset (Location Key))
    (before : Location Key → Word) (included : loop.entry.support ⊆ keys)
    (checked : loop.check = true) (current : before (.inl loop.activation) = loop.entryPoint)
    (bounded : (before (.inr loop.bound)).toNat ≤ loop.maximum) :
    ∃ invocation : Invocation loop.entry,
      CellEffects.system.Enables (encode keys before) invocation ∧
      CellEffects.system.fire (encode keys before) invocation = encode keys (loop.entryValues before) := by
  obtain ⟨invocation,enabled,fired⟩ := effect_realized loop.entry keys before (loop.entryValues before) included
    (loop.entryValues_guard before checked current bounded)
  rw [loop.entry_overwrite] at fired
  exact ⟨invocation,enabled,fired⟩

theorem Loop.entry_refuses_excess (loop : Loop Key) (before after : Location Key → Word)
    (excess : loop.maximum < (before (.inr loop.bound)).toNat) :
    loop.entry.guard (loop.entry.inputs.map before) (loop.entry.outputs.map after) ≠ true := by
  intro guarded
  have bounded := (loop.entry_guard_iff before after).mp guarded
  omega

def Loop.latchValues (loop : Loop Key) (before : Location Key → Word) : Location Key → Word :=
  Function.update (Function.update before (.inl loop.activation) loop.headerPoint)
    (.inr loop.index) (before (.inr loop.index) + 1)

theorem Loop.latchValues_guard (loop : Loop Key) (before : Location Key → Word)
    (checked : loop.check = true) (current : before (.inl loop.activation) = loop.latchPoint)
    (less : (before (.inr loop.index)).toNat < (before (.inr loop.bound)).toNat)
    (bounded : (before (.inr loop.bound)).toNat ≤ loop.maximum) :
    loop.latch.guard (loop.latch.inputs.map before) (loop.latch.outputs.map (loop.latchValues before)) = true := by
  apply (loop.latch_guard_iff before _).mpr
  exact ⟨checked, current, by simp [latchValues], less, bounded, by simp [latchValues]⟩

theorem Loop.latch_overwrite (loop : Loop Key) (before : Location Key → Word) :
    overwrite loop.latch.writes before (loop.latchValues before) = loop.latchValues before := by
  funext location
  cases location with
  | inl activation =>
    by_cases same : activation = loop.activation
    · subst activation
      simp [overwrite, Recipe.writes, latch, latchValues]
    · simp [overwrite, Recipe.writes, latch, latchValues, same]
  | inr key =>
    by_cases same : key = loop.index
    · subst key
      simp [overwrite, Recipe.writes, latch, latchValues]
    · simp [overwrite, Recipe.writes, latch, latchValues, same]

theorem Loop.latch_realized (loop : Loop Key) (keys : Finset (Location Key))
    (before : Location Key → Word) (included : loop.latch.support ⊆ keys)
    (checked : loop.check = true) (current : before (.inl loop.activation) = loop.latchPoint)
    (less : (before (.inr loop.index)).toNat < (before (.inr loop.bound)).toNat)
    (bounded : (before (.inr loop.bound)).toNat ≤ loop.maximum) :
    ∃ invocation : Invocation loop.latch,
      CellEffects.system.Enables (encode keys before) invocation ∧
      CellEffects.system.fire (encode keys before) invocation = encode keys (loop.latchValues before) ∧
      loop.rank (loop.latchValues before) < loop.rank before := by
  have guarded := loop.latchValues_guard before checked current less bounded
  obtain ⟨invocation, enabled, fired⟩ := effect_realized loop.latch keys before (loop.latchValues before) included guarded
  rw [loop.latch_overwrite] at fired
  refine ⟨invocation, enabled, fired, ?_⟩
  apply loop.latchStep_decreases before (loop.latchValues before)
  exact ⟨loop.latchValues before, guarded, (loop.latch_overwrite before).symm⟩

def Loop.headerValues (loop : Loop Key) (before : Location Key → Word) : Location Key → Word :=
  Function.update before (.inl loop.activation)
    (loop.headerTarget (before (.inr loop.index)) (before (.inr loop.bound)))

theorem Loop.headerValues_guard (loop : Loop Key) (before : Location Key → Word)
    (checked : loop.check = true) (current : before (.inl loop.activation) = loop.headerPoint)
    (ordered : (before (.inr loop.index)).toNat ≤ (before (.inr loop.bound)).toNat)
    (bounded : (before (.inr loop.bound)).toNat ≤ loop.maximum) :
    loop.header.guard (loop.header.inputs.map before) (loop.header.outputs.map (loop.headerValues before)) = true := by
  apply (loop.header_guard_iff before _).mpr
  exact ⟨checked, current, ordered, bounded, by simp [headerValues]⟩

theorem Loop.header_overwrite (loop : Loop Key) (before : Location Key → Word) :
    overwrite loop.header.writes before (loop.headerValues before) = loop.headerValues before := by
  funext location
  cases location with
  | inl activation =>
    by_cases same : activation = loop.activation
    · subst activation
      simp [overwrite, Recipe.writes, header, headerValues]
    · simp [overwrite, Recipe.writes, header, headerValues, same]
  | inr key => simp [overwrite, Recipe.writes, header, headerValues]

theorem Loop.header_realized (loop : Loop Key) (keys : Finset (Location Key))
    (before : Location Key → Word) (included : loop.header.support ⊆ keys)
    (checked : loop.check = true) (current : before (.inl loop.activation) = loop.headerPoint)
    (ordered : (before (.inr loop.index)).toNat ≤ (before (.inr loop.bound)).toNat)
    (bounded : (before (.inr loop.bound)).toNat ≤ loop.maximum) :
    ∃ invocation : Invocation loop.header,
      CellEffects.system.Enables (encode keys before) invocation ∧
      CellEffects.system.fire (encode keys before) invocation = encode keys (loop.headerValues before) := by
  obtain ⟨invocation, enabled, fired⟩ := effect_realized loop.header keys before (loop.headerValues before) included
    (loop.headerValues_guard before checked current ordered bounded)
  exact ⟨invocation, enabled, by simpa only [loop.header_overwrite] using fired⟩

namespace LoopControls

private def loop : Loop Nat := ⟨0, 1, 2, 3, 4, 5, 0, 1, 10⟩

example : loop.entry.guard [1, 10] [2, 0] = true := by decide
example : loop.entry.guard [1, 11] [2, 0] = false := by decide
example : loop.header.guard [2, 0, 0] [5] = true := by decide
example : loop.header.guard [2, 9, 10] [4] = true := by decide
example : loop.latch.guard [3, 9, 10] [2, 10] = true := by decide
example : loop.latch.guard [3, 10, 10] [2, 11] = false := by decide
example : ({ loop with bound := 0 }).check = false := by decide

private def keys : Finset (Location Nat) := {.inl 0,.inr 0,.inr 1}
private def lastIteration : Location Nat → Word
  | .inl _ => 3
  | .inr 0 => 9
  | .inr _ => 10
private def zeroBound : Location Nat → Word
  | .inl _ => 2
  | .inr _ => 0

theorem last_latch_fires : ∃ invocation : Invocation loop.latch,
    CellEffects.system.Enables (encode keys lastIteration) invocation ∧
    CellEffects.system.fire (encode keys lastIteration) invocation = encode keys (loop.latchValues lastIteration) ∧
    loop.rank (loop.latchValues lastIteration) = 0 := by
  obtain ⟨invocation, enabled, fired, _⟩ := loop.latch_realized keys lastIteration
    (by decide) (by decide) (by rfl) (by decide) (by decide)
  exact ⟨invocation, enabled, fired, by decide⟩

theorem zero_bound_exits : ∃ invocation : Invocation loop.header,
    CellEffects.system.Enables (encode keys zeroBound) invocation ∧
    CellEffects.system.fire (encode keys zeroBound) invocation = encode keys (loop.headerValues zeroBound) ∧
    loop.headerValues zeroBound (.inl 0) = loop.exitPoint := by
  obtain ⟨invocation, enabled, fired⟩ := loop.header_realized keys zeroBound
    (by decide) (by decide) (by rfl) (by decide) (by decide)
  exact ⟨invocation, enabled, fired, by decide⟩

end LoopControls

end Mettapedia.Machines.TIsa.Control
