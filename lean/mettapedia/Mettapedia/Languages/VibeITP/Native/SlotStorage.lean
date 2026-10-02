import Mettapedia.Languages.VibeITP.Spec.Protocol
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
Finite compact slot storage and the independent functional slot spaces.
The measured-capacity bridge supplies the access bounds. Allocation, pointed-to
record lifetime and release effects are separate native-memory interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.SlotStorage

open Spec

abbrev Slots (α : Type) := List (Option α)

def view {α : Type} (slots : Slots α) (index : Nat) : Option α :=
  slots[index]?.join

def Represents {α : Type} (slots : Slots α) (space : Nat → Option α) : Prop :=
  ∀ index, view slots index = space index

theorem view_outside {α : Type} (slots : Slots α) (index : Nat)
    (outside : slots.length ≤ index) : view slots index = none := by
  simp [view, List.getElem?_eq_none outside]

theorem view_inside {α : Type} (slots : Slots α) (index : Nat)
    (inside : index < slots.length) : view slots index = slots[index] := by
  simp [view, List.getElem?_eq_getElem inside]

theorem view_set {α : Type} (slots : Slots α) (index : Nat) (replacement : Option α)
    (inside : index < slots.length) :
    view (slots.set index replacement) = setSlot (view slots) index replacement := by
  funext candidate
  simp only [view, setSlot, List.getElem?_set]
  by_cases same : candidate = index
  · subst candidate
    simp [inside]
  · simp [same, Ne.symm same]

theorem represents_set {α : Type} (slots : Slots α) (space : Nat → Option α)
    (related : Represents slots space) (index : Nat) (replacement : Option α)
    (inside : index < slots.length) :
    Represents (slots.set index replacement) (setSlot space index replacement) := by
  intro candidate
  rw [view_set slots index replacement inside]
  simp only [setSlot, related candidate]

def exchange {α : Type} (slots : Slots α) (first second : Nat) : Slots α :=
  let prior := view slots first
  let updated := slots.set first (view slots second)
  updated.set second prior

theorem exchange_length {α : Type} (slots : Slots α) (first second : Nat) :
    (exchange slots first second).length = slots.length := by
  simp [exchange]

theorem view_exchange {α : Type} (slots : Slots α) (first second : Nat)
    (firstInside : first < slots.length) (secondInside : second < slots.length) :
    view (exchange slots first second) = swapSlots (view slots) first second := by
  unfold exchange
  rw [view_set _ second _ (by simpa using secondInside), view_set _ first _ firstInside]
  funext candidate
  by_cases same : first = second
  · subst second
    simp [setSlot, swapSlots]
  · by_cases atFirst : candidate = first
    · subst candidate
      simp [setSlot, swapSlots, same]
    · by_cases atSecond : candidate = second
      · subst candidate
        simp [setSlot, swapSlots, Ne.symm same]
      · simp [setSlot, swapSlots, atFirst, atSecond]

theorem represents_exchange {α : Type} (slots : Slots α) (space : Nat → Option α)
    (related : Represents slots space) (first second : Nat)
    (firstInside : first < slots.length) (secondInside : second < slots.length) :
    Represents (exchange slots first second) (swapSlots space first second) := by
  intro candidate
  rw [view_exchange slots first second firstInside secondInside]
  simp only [swapSlots, related first, related second, related candidate]

inductive Fault where
  | bounds
  | missing
  | occupied
  | buildFailed
  | previous (code : Nat)
  deriving DecidableEq, Repr

def read {α : Type} (slots : Slots α) (index : BitVec 64) : Except Fault α :=
  if index.toNat < slots.length then
    match slots[index.toNat]?.join with
    | none => .error .missing
    | some value => .ok value
  else .error .bounds

theorem read_matches_need {α : Type} (slots : Slots α) (space : Space)
    (index : BitVec 64) (inside : index.toNat < slots.length) :
    read slots index = (need space (view slots index.toNat)).mapError (fun _ => Fault.missing) := by
  unfold read
  rw [if_pos inside]
  cases value : view slots index.toNat <;> simp [need, view] at value ⊢
  all_goals rw [value]; rfl

def write {α : Type} (slots : Slots α) (index : BitVec 64) (value : α) :
    Except Fault (Slots α) :=
  if index.toNat < slots.length then
    if (view slots index.toNat).isSome then .error .occupied
    else .ok (slots.set index.toNat (some value))
  else .error .bounds

theorem write_ok_iff {α : Type} (slots : Slots α) (index : BitVec 64) (value : α)
    (after : Slots α) :
    write slots index value = .ok after ↔
      index.toNat < slots.length ∧ view slots index.toNat = none ∧
        after = slots.set index.toNat (some value) := by
  unfold write
  by_cases inside : index.toNat < slots.length
  · rw [if_pos inside]
    cases view slots index.toNat <;> simp [inside, eq_comm]
  · simp [inside]

theorem write_preserves_representation {α : Type} (slots : Slots α)
    (space : Nat → Option α) (related : Represents slots space)
    (index : BitVec 64) (value : α) (after : Slots α)
    (completed : write slots index value = .ok after) :
    Represents after (setSlot space index.toNat (some value)) := by
  rcases (write_ok_iff slots index value after).mp completed with ⟨inside, _, updated⟩
  rw [updated]
  exact represents_set slots space related index.toNat (some value) inside

/-- Ordered validation of a native publication. Ownership release is an effect
of the caller and does not change the surviving slot-array projection. -/
def publish {α : Type} (previous : Nat) (slots : Slots α) (index : BitVec 64)
    (candidate : Option α) : Except Fault (Slots α) :=
  if previous ≠ 0 then .error (.previous previous)
  else match candidate with
    | none => .error .buildFailed
    | some value => write slots index value

theorem publish_ok_iff {α : Type} (previous : Nat) (slots : Slots α)
    (index : BitVec 64) (candidate : Option α) (after : Slots α) :
    publish previous slots index candidate = .ok after ↔
      previous = 0 ∧ ∃ value, candidate = some value ∧ write slots index value = .ok after := by
  unfold publish
  by_cases clear : previous = 0
  · subst previous
    cases candidate <;> simp
  · simp [clear]

theorem publish_does_not_overwrite {α : Type} (previous : Nat) (slots : Slots α)
    (index : BitVec 64) (candidate : Option α) (after : Slots α)
    (completed : publish previous slots index candidate = .ok after) :
    view slots index.toNat = none := by
  rcases (publish_ok_iff previous slots index candidate after).mp completed with ⟨_, value, _, written⟩
  exact ((write_ok_iff slots index value after).mp written).2.1

def clear {α : Type} (slots : Slots α) (index : BitVec 64) : Except Fault (Slots α) := do
  let _ ← read slots index
  .ok (slots.set index.toNat none)

theorem clear_ok_iff {α : Type} (slots : Slots α) (index : BitVec 64) (after : Slots α) :
    clear slots index = .ok after ↔
      index.toNat < slots.length ∧ (view slots index.toNat).isSome = true ∧
        after = slots.set index.toNat none := by
  unfold clear read
  by_cases inside : index.toNat < slots.length
  · rw [if_pos inside]
    change (match view slots index.toNat with
      | none => Except.error Fault.missing
      | some value => Except.ok value) >>= (fun _ => Except.ok (slots.set index.toNat none)) =
        .ok after ↔ _
    cases view slots index.toNat <;> simp [inside, eq_comm, bind, Except.bind]
  · simp [inside, bind, Except.bind]

theorem clear_preserves_representation {α : Type} (slots : Slots α)
    (space : Nat → Option α) (related : Represents slots space)
    (index : BitVec 64) (after : Slots α) (completed : clear slots index = .ok after) :
    Represents after (setSlot space index.toNat none) := by
  rcases (clear_ok_iff slots index after).mp completed with ⟨inside, _, updated⟩
  rw [updated]
  exact represents_set slots space related index.toNat none inside

theorem null_publication_precedes_bounds :
    publish 0 ([] : Slots Nat) 0 none = .error .buildFailed := rfl

theorem previous_failure_precedes_null :
    publish 6 ([] : Slots Nat) 0 none = .error (.previous 6) := rfl

theorem occupied_publication_rejects :
    publish 0 [some (4 : Nat)] 0 (some 9) = .error .occupied := rfl

theorem self_exchange_keeps_occupied : exchange [some (4 : Nat)] 0 0 = [some 4] := rfl

theorem exchange_keeps_empty_slots :
    exchange [some (4 : Nat), none] 0 1 = [none, some 4] := rfl

theorem read_empty_is_missing : read [none] (0 : BitVec 64) = (.error .missing : Except Fault Nat) := rfl

theorem read_outside_is_bounds : read [some (4 : Nat)] 1 = .error .bounds := rfl

end Mettapedia.Languages.VibeITP.Native.SlotStorage
