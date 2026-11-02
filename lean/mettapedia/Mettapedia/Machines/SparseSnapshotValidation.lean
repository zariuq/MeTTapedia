import Mathlib.Data.List.Nodup

/-!
# Full-slot validation for bounded sparse snapshots

An occupied-entry count is not a bound on the indices of occupied slots.
This executable checker visits the entire storage list, checks each occupied
record, and separately checks the declared count and unique identities.

The semantic condition quantifies over every stored slot. The soundness theorem
connects that condition to the Boolean traversal. The original prefix traversal
has a concrete sparse-tail counterexample; a well-formed sparse snapshot is a
positive control. These are shape laws, not authority, checksum or C refinement
claims. Native record decoding and publication require their own checks.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SparseSnapshotValidation

structure Slot where
  present : Nat
  identity : Nat
  scene : Nat
  activeTab : Nat
  tabCount : Nat
  flags : Nat
  deriving DecidableEq, Repr

def Slot.Valid (scenes tabs : Nat) (slot : Slot) : Prop :=
  slot.present = 0 ∨
    (slot.present = 1 ∧ slot.scene < scenes ∧ 0 < slot.tabCount ∧
      slot.tabCount ≤ tabs ∧ slot.activeTab < slot.tabCount ∧ slot.flags < 8)

def Slot.check (scenes tabs : Nat) (slot : Slot) : Bool :=
  if slot.present = 0 then true else
    decide (slot.present = 1) && decide (slot.scene < scenes) &&
      decide (0 < slot.tabCount) && decide (slot.tabCount ≤ tabs) &&
      decide (slot.activeTab < slot.tabCount) && decide (slot.flags < 8)

theorem Slot.check_iff (scenes tabs : Nat) (slot : Slot) :
    slot.check scenes tabs = true ↔ slot.Valid scenes tabs := by
  by_cases empty : slot.present = 0
  · simp [Slot.check, Slot.Valid, empty]
  · simp [Slot.check, Slot.Valid, empty, and_assoc]

structure Snapshot where
  activeScene : Nat
  declaredCount : Nat
  slots : List Slot
  deriving DecidableEq, Repr

def identities (slots : List Slot) : List Nat :=
  slots.filterMap fun slot => if slot.present = 0 then none else some slot.identity

def Snapshot.Valid (bound scenes tabs : Nat) (snapshot : Snapshot) : Prop :=
  snapshot.activeScene < scenes ∧ snapshot.slots.length = bound ∧
    snapshot.declaredCount ≤ bound ∧
    (∀ slot ∈ snapshot.slots, slot.Valid scenes tabs) ∧
    (identities snapshot.slots).length = snapshot.declaredCount ∧
    (identities snapshot.slots).Nodup

def Snapshot.check (bound scenes tabs : Nat) (snapshot : Snapshot) : Bool :=
  decide (snapshot.activeScene < scenes) && decide (snapshot.slots.length = bound) &&
    decide (snapshot.declaredCount ≤ bound) && snapshot.slots.all (Slot.check scenes tabs) &&
    decide ((identities snapshot.slots).length = snapshot.declaredCount) &&
    decide ((identities snapshot.slots).Nodup)

theorem Snapshot.check_iff (bound scenes tabs : Nat) (snapshot : Snapshot) :
    snapshot.check bound scenes tabs = true ↔ snapshot.Valid bound scenes tabs := by
  simp [Snapshot.check, Snapshot.Valid, List.all_eq_true, Slot.check_iff, and_assoc]

theorem accepted_slot (bound scenes tabs : Nat) (snapshot : Snapshot)
    (accepted : snapshot.check bound scenes tabs = true)
    (slot : Slot) (member : slot ∈ snapshot.slots) :
    slot.Valid scenes tabs :=
  ((Snapshot.check_iff bound scenes tabs snapshot).mp accepted).2.2.2.1 slot member

/-- Every tab loop in every occupied slot has its declared upper bound,
including slots beyond the occupied-entry count. -/
theorem accepted_tab_bounds (bound scenes tabs : Nat) (snapshot : Snapshot)
    (accepted : snapshot.check bound scenes tabs = true)
    (slot : Slot) (member : slot ∈ snapshot.slots) (occupied : slot.present ≠ 0) :
    slot.present = 1 ∧ 0 < slot.tabCount ∧ slot.tabCount ≤ tabs ∧
      slot.activeTab < slot.tabCount := by
  rcases accepted_slot bound scenes tabs snapshot accepted slot member with empty | valid
  · exact False.elim (occupied empty)
  · exact ⟨valid.1, valid.2.2.1, valid.2.2.2.1, valid.2.2.2.2.1⟩

theorem accepted_count_and_unique (bound scenes tabs : Nat) (snapshot : Snapshot)
    (accepted : snapshot.check bound scenes tabs = true) :
    (identities snapshot.slots).length = snapshot.declaredCount ∧
      (identities snapshot.slots).Nodup :=
  ((Snapshot.check_iff bound scenes tabs snapshot).mp accepted).2.2.2.2

/-- The prefix policy checks at most `declaredCount` physical indices; it
does not establish that later indices are unoccupied. -/
def prefixCheck (bound scenes tabs : Nat) (snapshot : Snapshot) : Bool :=
  decide (snapshot.slots.length = bound) && decide (snapshot.declaredCount ≤ bound) &&
    decide (snapshot.activeScene < scenes) &&
    (snapshot.slots.take snapshot.declaredCount).all (fun slot =>
      if slot.present = 0 then true else
        decide (slot.tabCount ≤ tabs) && decide (slot.activeTab < slot.tabCount) &&
          decide (slot.flags < 8))

def emptySlot : Slot := ⟨0, 0, 0, 0, 0, 0⟩
def sparse (tabCount : Nat) : Snapshot :=
  ⟨0, 1, List.replicate 8 emptySlot ++ [⟨1, 73, 0, 0, tabCount, 0⟩]⟩

theorem original_sparse_tail_counterexample :
    prefixCheck 9 5 8 (sparse 255) = true ∧
      (sparse 255).check 9 5 8 = false ∧
      ∃ slot ∈ (sparse 255).slots, slot.present ≠ 0 ∧ 8 < slot.tabCount := by
  decide

theorem well_formed_sparse_accepted : (sparse 1).check 9 5 8 = true := by
  decide

theorem duplicate_identity_refused :
    (Snapshot.mk 0 2 [⟨1, 73, 0, 0, 1, 0⟩, ⟨1, 73, 0, 0, 1, 0⟩]).check 2 5 8 = false := by
  decide

theorem incorrect_count_refused :
    (Snapshot.mk 0 2 (sparse 1).slots).check 9 5 8 = false := by
  decide

end Mettapedia.Machines.SparseSnapshotValidation
