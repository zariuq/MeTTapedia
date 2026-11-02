import Mettapedia.Machines.Cursor.IndexedIntersection

/-!
# Exact payload positions from a distinct-key range

Binary lower-bound navigation returns a position only after equality is
checked. A nearest greater key is not a successful lookup. The returned
position can index a parallel payload array without searching its values.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.IndexedKeyLookup

open IndexedIntersection
open Mettapedia.GSLT.Dynamics.RelationalKeyRanges

variable {Key : Type*} [LinearOrder Key]

def lookup (range : Range Key) (target : Key) : Option Nat × Nat :=
  let sought := range.seek target
  if 0 < sought.1.width then
    (if sought.1.read sought.1.lo = target then some sought.1.lo else none, sought.2 + 1)
  else (none, sought.2)

theorem initial (range : Range Key) (sorted : range.Sorted) (target : Key) :
    InitialSegment (fun i => decide (range.read i < target)) range.lo range.hi := by
  intro i j lower ascending upper accepted
  simp only [decide_eq_true_eq] at accepted ⊢
  by_cases same : i = j
  · simpa [same] using accepted
  · exact (sorted i j lower (by omega) upper).trans accepted

theorem seek_position (range : Range Key) (sorted : range.Sorted) (target : Key)
    (i : Nat) (lower : range.lo ≤ i) (upper : i < range.hi) (equal : range.read i = target) :
    (range.seek target).1.lo = i := by
  obtain ⟨low, high, before, after⟩ :=
    binaryPartition_correct _ range.lo range.hi (initial range sorted target) range.bounds
  change (binaryPartition _ range.lo range.hi).1 = i
  apply Nat.le_antisymm
  · by_contra wrong
    have impossible := before i lower (by omega)
    simp [equal] at impossible
  · by_contra wrong
    have earlier : (binaryPartition (fun j => decide (range.read j < target)) range.lo range.hi).1 < i := by omega
    have less := sorted _ i low earlier upper
    have notBefore := after _ le_rfl (earlier.trans upper)
    simp only [decide_eq_false_iff_not] at notBefore
    exact notBefore (by simpa [equal] using less)

theorem lookup_some_iff (range : Range Key) (sorted : range.Sorted) (target : Key) (i : Nat) :
    (lookup range target).1 = some i ↔ range.lo ≤ i ∧ i < range.hi ∧ range.read i = target := by
  constructor
  · intro found
    dsimp only [lookup] at found
    split at found
    next active =>
      dsimp only at found
      split at found
      next equal =>
        have same := Option.some.inj found
        have bounds := partition_bounds (fun j => decide (range.read j < target))
          range.lo range.hi range.bounds
        change (range.seek target).1.lo = i at same
        have lower : range.lo ≤ (range.seek target).1.lo := bounds.1
        have upper : (range.seek target).1.lo < range.hi := by
          change 0 < range.hi - (range.seek target).1.lo at active
          omega
        change range.read (range.seek target).1.lo = target at equal
        exact ⟨by omega, by omega, by simpa [same] using equal⟩
      · cases found
    · cases found
  · rintro ⟨lower, upper, equal⟩
    have position := seek_position range sorted target i lower upper equal
    have active : 0 < (range.seek target).1.width := by
      change 0 < range.hi - (range.seek target).1.lo
      omega
    have atKey : (range.seek target).1.read (range.seek target).1.lo = target := by
      change range.read (range.seek target).1.lo = target
      simpa [position] using equal
    dsimp only [lookup]
    rw [if_pos active]
    dsimp only
    rw [if_pos atKey, position]

theorem lookup_none_iff (range : Range Key) (sorted : range.Sorted) (target : Key) :
    (lookup range target).1 = none ↔ target ∉ range.view := by
  constructor
  · intro missing member
    obtain ⟨i, lower, upper, equal⟩ := (mem_view range target).mp member
    have found := (lookup_some_iff range sorted target i).mpr ⟨lower, upper, equal⟩
    rw [missing] at found
    cases found
  · intro absent
    cases result : (lookup range target).1 with
    | none => rfl
    | some i =>
        obtain ⟨lower, upper, equal⟩ := (lookup_some_iff range sorted target i).mp result
        exact False.elim (absent ((mem_view range target).mpr ⟨i, lower, upper, equal⟩))

theorem lookup_comparisons (range : Range Key) (target : Key) (maximum : Nat)
    (bounded : range.width ≤ maximum) :
    (lookup range target).2 ≤ seekBudget maximum + 1 := by
  have charge := seek_comparisons range target (seekBudget maximum)
    (width_lt_budget range maximum bounded)
  dsimp only [lookup]
  split <;> simp only <;> omega

namespace Controls

def keys : Range Nat := Range.ofArray #[1, 4, 9] 0

theorem exact_position : (lookup keys 4).1 = some 1 := by decide +kernel
theorem nearest_greater_is_not_a_match : (lookup keys 3).1 = none := by decide +kernel
theorem past_end_is_not_a_match : (lookup keys 10).1 = none := by decide +kernel
theorem empty_is_absent : (lookup (Range.ofArray (#[] : Array Nat) 0) 0).1 = none := by decide +kernel

end Controls

end Mettapedia.Machines.Cursor.IndexedKeyLookup
