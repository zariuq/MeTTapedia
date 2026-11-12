import Mettapedia.Machines.HybridShapeStore
import Mathlib.Tactic

/-!
# Atomic removal across compact facts and ordinary copies

The carrier is the existing hybrid store. The capacity contract reserves one
staging slot per selected ordinary occurrence before either representation
changes. A compact-only target needs no such slots and can use the existing
direct removal operation. Capacity is a model of available reservation, not a
proof of native allocator behavior.

The interpretation is a bag observation and retains multiplicity. It does not
establish native row order, occurrence-pointer lifetime or thread safety.
Atomic refusal belongs to this primitive; it does not roll back earlier calls.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HybridStorePublication

open HybridShapeStore
variable {Fact : Type}

def required (select : Fact → Bool) (store : Store Fact) : Nat :=
  (store.rows.filter fun fact => select fact = true).card

def contract (select : Fact → Bool) (store : Store Fact) : Store Fact :=
  ⟨store.compact.filter (fun fact => select fact = false),
    store.rows.filter (fun fact => select fact = false)⟩

def selectedCount (select : Fact → Bool) (store : Store Fact) : Nat :=
  (store.compact.filter (fun fact => select fact = true)).card + required select store

/-- Refusal returns the unchanged input store. Only an admitted reservation
can publish both parts of this one primitive update. -/
def removeAll (select : Fact → Bool) (capacity : Nat) (store : Store Fact) : Option Nat × Store Fact :=
  if required select store ≤ capacity then (some (selectedCount select store), contract select store)
  else (none, store)

theorem contract_observation (select : Fact → Bool) (store : Store Fact) :
    denote (contract select store) = (denote store).filter (fun fact => select fact = false) := by
  simp [contract, denote, Multiset.filter_add]

theorem selected_count_observation (select : Fact → Bool) (store : Store Fact) :
    selectedCount select store = ((denote store).filter (fun fact => select fact = true)).card := by
  simp only [selectedCount, required, denote, Multiset.filter_add, Multiset.card_add]
  rfl

theorem accepted_iff (select : Fact → Bool) (capacity : Nat) (store : Store Fact) :
    (removeAll select capacity store).1.isSome = true ↔ required select store ≤ capacity := by
  by_cases room : required select store ≤ capacity <;> simp [removeAll, room]

theorem refused_preserves_store (select : Fact → Bool) (capacity : Nat) (store : Store Fact)
    (refused : (removeAll select capacity store).1 = none) :
    (removeAll select capacity store).2 = store := by
  unfold removeAll at refused ⊢
  split_ifs <;> simp_all

theorem accepted_observation (select : Fact → Bool) (capacity : Nat) (store : Store Fact)
    (count : Nat) (accepted : (removeAll select capacity store).1 = some count) :
    denote (removeAll select capacity store).2 =
        (denote store).filter (fun fact => select fact = false) ∧
      count = ((denote store).filter (fun fact => select fact = true)).card := by
  by_cases room : required select store ≤ capacity
  · have counted : selectedCount select store = count := by
      simpa [removeAll, room] using accepted
    simpa only [removeAll, if_pos room] using
      And.intro (contract_observation select store)
        (counted.symm.trans (selected_count_observation select store))
  · simp [removeAll, room] at accepted

theorem accepted_partition (select : Fact → Bool) (capacity : Nat) (store : Store Fact)
    (count : Nat) (accepted : (removeAll select capacity store).1 = some count) :
    (denote (removeAll select capacity store).2).card + count = (denote store).card := by
  obtain ⟨result, counted⟩ := accepted_observation select capacity store count accepted
  rw [result, counted]
  have partition := Multiset.filter_add_not (fun fact => select fact = true) (denote store)
  have cards := congrArg Multiset.card partition
  simpa [Multiset.card_add, Bool.not_eq_true, Nat.add_comm] using cards

theorem no_rows_need_no_staging (select : Fact → Bool) (compact : Finset Fact) :
    required select ⟨compact, 0⟩ = 0 ∧
      (removeAll select 0 ⟨compact, 0⟩).1 = some ((compact.filter (fun fact => select fact = true)).card) := by
  simp [required, removeAll, selectedCount]

variable [DecidableEq Fact]

theorem no_matching_rows_need_no_staging (fact : Fact) (store : Store Fact)
    (absent : fact ∉ store.rows) : required (fun other => decide (other = fact)) store = 0 := by
  simp only [required, decide_eq_true_eq, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro other present same
  subst other
  exact absent present

/-- With no ordinary copy of this value, the existing direct single-copy
operation is also the complete all-copy removal. Other ordinary values remain. -/
theorem compact_target_direct (fact : Fact) (store : Store Fact)
    (absent : fact ∉ store.rows) :
    (removeAll (fun other => decide (other = fact)) 0 store).2 = (removeOne fact store).2 := by
  have room := no_matching_rows_need_no_staging fact store absent
  have ordinary : store.rows.filter (fun other => decide (other = fact) = false) = store.rows := by
    apply Multiset.filter_eq_self.mpr
    intro other present
    simp only [decide_eq_false_iff_not]
    intro same
    subst other
    exact absent present
  have compact : store.compact.filter (fun other => decide (other = fact) = false) =
      store.compact.erase fact := by
    ext other
    simp [and_comm, eq_comm]
  by_cases present : fact ∈ store.compact
  · simp only [removeAll, room, Nat.le_refl, if_true, contract, ordinary, compact,
      removeOne, if_pos present]
  · simp only [removeAll, room, Nat.le_refl, if_true, contract, ordinary, compact,
      removeOne, if_neg present, if_neg absent, Finset.erase_eq_of_notMem present]

theorem compact_target_result (fact : Fact) (store : Store Fact)
    (absent : fact ∉ store.rows) :
    (removeAll (fun other => decide (other = fact)) 0 store).1 =
      some (if (removeOne fact store).1 then 1 else 0) := by
  have room := no_matching_rows_need_no_staging fact store absent
  by_cases present : fact ∈ store.compact
  · have chosen : store.compact.filter (fun other => decide (other = fact) = true) = {fact} := by
      ext other
      simp only [Finset.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
      exact ⟨fun both => both.2, fun same => ⟨same ▸ present, same⟩⟩
    simp only [removeAll, room, Nat.le_refl, if_true, selectedCount, chosen,
      Finset.card_singleton, Nat.add_zero, removeOne, if_pos present]
  · have chosen : store.compact.filter (fun other => decide (other = fact) = true) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro other member
      simp only [decide_eq_true_eq]
      intro same
      subst other
      exact present member
    simp only [removeAll, room, Nat.le_refl, if_true, selectedCount, chosen,
      Finset.card_empty, Nat.add_zero, removeOne, if_neg present, if_neg absent,
      Bool.false_eq_true, if_false]

/-- A deliberate incorrect ordering: the compact part changes before the
ordinary reservation can refuse. It is a negative control, not a fallback. -/
def denseFirst (select : Fact → Bool) (capacity : Nat) (store : Store Fact) : Option Nat × Store Fact :=
  let intermediate : Store Fact := ⟨(contract select store).compact, store.rows⟩
  if required select store ≤ capacity then (some (selectedCount select store), contract select store)
  else (none, intermediate)

namespace Controls

def mixed : Store Nat := ⟨{7}, {7, 8}⟩

theorem mixed_refusal_is_atomic :
    (removeAll (· == 7) 0 mixed).1 = none ∧
      (denote (removeAll (· == 7) 0 mixed).2).count 7 = 2 := by decide

theorem dense_first_loses_a_copy_on_refusal :
    (denseFirst (· == 7) 0 mixed).1 = none ∧
      (denote (denseFirst (· == 7) 0 mixed).2).count 7 = 1 := by decide

theorem adequate_reservation_removes_both_copies :
    (removeAll (· == 7) 1 mixed).1 = some 2 ∧
      denote (removeAll (· == 7) 1 mixed).2 = {8} := by decide

theorem later_refusal_keeps_an_earlier_addition :
    let after := add 9 mixed
    (removeAll (· == 7) 0 after).1 = none ∧
      (denote (removeAll (· == 7) 0 after).2).count 9 = 1 := by decide

end Controls

end Mettapedia.Machines.HybridStorePublication
