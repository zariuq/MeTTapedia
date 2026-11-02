import Mettapedia.Machines.Cursor.IndexedIntersection
import Mettapedia.Machines.PolyCursor
import Mathlib.Data.List.MinMax

/-!
# Minimum-projection probing as an indexed intersection route

This route scans the smallest distinct-key range and binary-probes all
participating ranges. It is a different physical algorithm from cyclic
leapfrog, with the same support observation. Its explicit width factor is
the number of participating ranges. Input occurrence multiplicities belong
to the query's independent provenance layer, not to these distinct keys.

Index preparation, constant-time reader access and range lifetime must be
justified by the caller. The comparison ledger includes every binary probe;
it does not hide projection construction inside a unit-cost operation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.IndexedMultiwayProjection

open IndexedIntersection
open Mettapedia.GSLT.Dynamics.RelationalKeyRanges

variable {Key : Type} [LinearOrder Key]

def probe (r : Range Key) (key : Key) : Bool × Nat :=
  let sought := r.seek key
  (if sought.1.lo < sought.1.hi then decide (sought.1.read sought.1.lo = key) else false,
   sought.2)

theorem probe_exact (r : Range Key) (key : Key) (sorted : r.Sorted) :
    (probe r key).1 = true ↔ key ∈ r.view := by
  have initial : InitialSegment (fun i => decide (r.read i < key)) r.lo r.hi := by
    intro i j lo ascending hi accepted
    simp only [decide_eq_true_eq] at accepted ⊢
    by_cases same : i = j
    · simpa [same] using accepted
    · exact (sorted i j lo (by omega) hi).trans accepted
  obtain ⟨lower, upper, before, after⟩ :=
    binaryPartition_correct _ r.lo r.hi initial r.bounds
  rw [mem_view]
  change (if (binaryPartition (fun i => decide (r.read i < key)) r.lo r.hi).1 < r.hi
    then decide (r.read (binaryPartition (fun i => decide (r.read i < key)) r.lo r.hi).1 = key)
    else false) = true ↔ _
  by_cases inRange : (binaryPartition (fun i => decide (r.read i < key)) r.lo r.hi).1 < r.hi
  · rw [if_pos inRange]
    simp only [decide_eq_true_eq]
    constructor
    · intro same
      exact ⟨_, lower, inRange, same⟩
    · rintro ⟨i, lo, hi, same⟩
      have position : (binaryPartition (fun j => decide (r.read j < key)) r.lo r.hi).1 ≤ i := by
        by_contra missed
        have smaller := before i lo (Nat.lt_of_not_ge missed)
        simp [same] at smaller
      by_cases equal : (binaryPartition (fun j => decide (r.read j < key)) r.lo r.hi).1 = i
      · simpa [equal] using same
      · have smaller := sorted _ i lower (lt_of_le_of_ne position equal) hi
        have notSmaller := after _ le_rfl inRange
        simp only [decide_eq_false_iff_not] at notSmaller
        exact False.elim (notSmaller (by simpa [same] using smaller))
  · rw [if_neg inRange]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro i lo hi same
    have smaller := before i lo (by omega)
    simp [same] at smaller

theorem probe_comparisons (r : Range Key) (key : Key) (k : Nat)
    (bounded : r.width < 2 ^ k) : (probe r key).2 ≤ k :=
  seek_comparisons r key k bounded

def probeAll : List (Range Key) → Key → Bool × Nat
  | [], _ => (true, 0)
  | r :: rest, key =>
      let here := probe r key
      let later := probeAll rest key
      (here.1 && later.1, here.2 + later.2)

theorem probeAll_exact (ranges : List (Range Key)) (key : Key)
    (sorted : ∀ r ∈ ranges, r.Sorted) :
    (probeAll ranges key).1 = true ↔ ∀ r ∈ ranges, key ∈ r.view := by
  induction ranges with
  | nil => simp [probeAll]
  | cons r rest ih =>
      simp only [probeAll, Bool.and_eq_true, List.forall_mem_cons]
      rw [probe_exact r key (sorted r (by simp)), ih (fun s h => sorted s (by simp [h]))]

theorem probeAll_comparisons (ranges : List (Range Key)) (key : Key) (k : Nat)
    (bounded : ∀ r ∈ ranges, r.width < 2 ^ k) :
    (probeAll ranges key).2 ≤ ranges.length * k := by
  induction ranges with
  | nil => simp [probeAll]
  | cons r rest ih =>
      have head := probe_comparisons r key k (bounded r (by simp))
      have tail := ih (fun s h => bounded s (by simp [h]))
      simp only [probeAll, List.length_cons]
      nlinarith

structure Result (Key : Type*) where
  keys : List Key
  comparisons : Nat
  deriving Repr, DecidableEq

/-- Scan exactly `remaining` positions of a prepared range. This argument is
a range length, not an interrupt budget: there is no success on cutoff. -/
def scan (read : Nat → Key) (ranges : List (Range Key)) : Nat → Nat → Result Key
  | 0, _ => ⟨[], 0⟩
  | remaining + 1, position =>
      let key := read position
      let here := probeAll ranges key
      let later := scan read ranges remaining (position + 1)
      ⟨if here.1 then key :: later.keys else later.keys, here.2 + later.comparisons⟩

theorem scan_keys (read : Nat → Key) (ranges : List (Range Key)) (remaining position : Nat) :
    (scan read ranges remaining position).keys =
      ((List.range' position remaining).map read).filter (fun key => (probeAll ranges key).1) := by
  induction remaining generalizing position with
  | zero => simp [scan]
  | succ remaining ih =>
      simp only [scan, List.range'_succ, List.map_cons, List.filter_cons]
      rw [ih]

theorem scan_comparisons (read : Nat → Key) (ranges : List (Range Key))
    (remaining position k : Nat) (bounded : ∀ r ∈ ranges, r.width < 2 ^ k) :
    (scan read ranges remaining position).comparisons ≤ remaining * ranges.length * k := by
  induction remaining generalizing position with
  | zero => simp [scan]
  | succ remaining ih =>
      have here := probeAll_comparisons ranges (read position) k bounded
      have later := ih (position + 1)
      simp only [scan]
      nlinarith

def selected (ranges : List (Range Key)) : Option (Range Key) := ranges.argmin Range.width

def intersect (ranges : List (Range Key)) : Option (Result Key) :=
  (selected ranges).map fun seed => scan seed.read ranges seed.width seed.lo

omit [LinearOrder Key] in
theorem selected_member {ranges : List (Range Key)} {seed : Range Key}
    (chosen : selected ranges = some seed) : seed ∈ ranges := List.argmin_mem chosen

omit [LinearOrder Key] in
theorem selected_minimal {ranges : List (Range Key)} {seed : Range Key}
    (chosen : selected ranges = some seed) (r : Range Key) (member : r ∈ ranges) :
    seed.width ≤ r.width := List.le_of_mem_argmin member chosen

theorem empty_family_declines : intersect ([] : List (Range Key)) = none := rfl

theorem selected_spec {ranges : List (Range Key)} {seed : Range Key}
    (chosen : selected ranges = some seed) (sorted : ∀ r ∈ ranges, r.Sorted)
    (k : Nat) (bounded : ∀ r ∈ ranges, r.width < 2 ^ k) :
    let result := scan seed.read ranges seed.width seed.lo
    intersect ranges = some result ∧
      (∀ key, key ∈ result.keys ↔ ∀ r ∈ ranges, key ∈ r.view) ∧
      result.keys.Pairwise (· < ·) ∧
      result.comparisons ≤ seed.width * ranges.length * k := by
  dsimp only
  have seedMember := selected_member chosen
  have equation : (scan seed.read ranges seed.width seed.lo).keys =
      seed.view.filter (fun key => (probeAll ranges key).1) := scan_keys ..
  refine ⟨by simp [intersect, chosen], ?_, ?_,
    scan_comparisons seed.read ranges seed.width seed.lo k bounded⟩
  · intro key
    rw [equation, List.mem_filter, probeAll_exact ranges key sorted]
    exact and_iff_right_of_imp (fun all => all seed seedMember)
  · rw [equation]
    exact (view_sorted seed (sorted seed seedMember)).sublist (List.filter_sublist)

/-- The selected route observes exactly the same support as the existing
multiway leapfrog. This equality does not identify their execution traces. -/
theorem agrees_with_leapfrog {ranges : List (Range Key)} {seed : Range Key}
    (chosen : selected ranges = some seed) (sorted : ∀ r ∈ ranges, r.Sorted) :
    (scan seed.read ranges seed.width seed.lo).keys.toFinset =
      (Mettapedia.Machines.PolyCursor.leapfrog (ranges.map Range.view)).toFinset := by
  have equation : (scan seed.read ranges seed.width seed.lo).keys =
      seed.view.filter (fun key => (probeAll ranges key).1) := scan_keys ..
  ext key
  simp only [List.mem_toFinset]
  rw [Mettapedia.Machines.PolyCursor.mem_leapfrog
    (Mettapedia.Machines.PolyCursor.total _) _ le_rfl]
  · rw [equation, List.mem_filter, probeAll_exact ranges key sorted]
    have nonempty : ranges.map Range.view ≠ [] := by
      have := selected_member chosen
      intro empty
      have : ranges = [] := List.map_eq_nil_iff.mp empty
      simp_all
    simp only [List.forall_mem_map]
    constructor
    · rintro ⟨_, all⟩
      exact ⟨nonempty, all⟩
    · rintro ⟨_, all⟩
      exact ⟨all seed (selected_member chosen), all⟩
  · intro keys member
    obtain ⟨r, present, rfl⟩ := List.mem_map.mp member
    exact view_sorted r (sorted r present)

def minimumWidth (ranges : List (Range Key)) : Nat :=
  match selected ranges with
  | none => 0
  | some seed => seed.width

def comparisons (ranges : List (Range Key)) : Nat :=
  match intersect ranges with
  | none => 0
  | some result => result.comparisons

def keys (ranges : List (Range Key)) : List Key :=
  match intersect ranges with
  | none => []
  | some result => result.keys

/-- Refusal has its own status in `intersect`; these projections are ledger
fields and do not turn a refused plan into a successful empty observation. -/
theorem comparisons_bound (ranges : List (Range Key)) (maximum : Nat)
    (bounded : ∀ r ∈ ranges, r.width ≤ maximum) :
    comparisons ranges ≤ minimumWidth ranges * ranges.length * seekBudget maximum := by
  cases chosen : selected ranges with
  | none => simp [comparisons, intersect, minimumWidth, chosen]
  | some seed =>
      simp only [comparisons, intersect, minimumWidth, chosen, Option.map_some]
      exact scan_comparisons seed.read ranges seed.width seed.lo (seekBudget maximum)
        (fun r member => width_lt_budget r maximum (bounded r member))

/-- Ranking, scanning, probe boundary/equality tests and output delivery are
charged in addition to binary midpoint comparisons. -/
def workBound (ranges : List (Range Key)) : Nat :=
  ranges.length + minimumWidth ranges * (1 + 2 * ranges.length) +
    comparisons ranges + (keys ranges).length

theorem work_bound (ranges : List (Range Key)) (maximum : Nat)
    (bounded : ∀ r ∈ ranges, r.width ≤ maximum) :
    workBound ranges ≤ ranges.length +
      minimumWidth ranges * (1 + ranges.length * (2 + seekBudget maximum)) +
        (keys ranges).length := by
  have charge := comparisons_bound ranges maximum bounded
  dsimp [workBound]
  nlinarith

def sumMin (stages : List (List (Range Key))) : Nat := (stages.map minimumWidth).sum

def delivered (stages : List (List (Range Key))) : Nat :=
  (stages.map fun ranges => (keys ranges).length).sum

theorem keys_length_le_minimum (ranges : List (Range Key)) :
    (keys ranges).length ≤ minimumWidth ranges := by
  cases chosen : selected ranges with
  | none => simp [keys, intersect, minimumWidth, chosen]
  | some seed =>
      simp only [keys, intersect, minimumWidth, chosen, Option.map_some]
      rw [scan_keys]
      exact (List.length_filter_le _ _).trans_eq (by simp)

theorem delivered_le_sumMin (stages : List (List (Range Key))) :
    delivered stages ≤ sumMin stages := by
  induction stages with
  | nil => rfl
  | cons ranges rest ih =>
      have head := keys_length_le_minimum ranges
      simp only [sumMin, delivered, List.map_cons, List.sum_cons] at *
      omega

theorem keys_sorted (ranges : List (Range Key)) (sorted : ∀ r ∈ ranges, r.Sorted) :
    (keys ranges).Pairwise (· < ·) := by
  cases chosen : selected ranges with
  | none => simp [keys, intersect, chosen]
  | some seed =>
      simp only [keys, intersect, chosen, Option.map_some]
      rw [scan_keys]
      exact (view_sorted seed (sorted seed (selected_member chosen))).sublist List.filter_sublist

/-- A finite sum-min account for actual prepared stages. Query-width and
per-stage setup remain explicit; constructing those stages is not free. -/
theorem sum_min_work_bound (stages : List (List (Range Key))) (maximum width : Nat)
    (bounded : ∀ ranges ∈ stages, ∀ r ∈ ranges, r.width ≤ maximum)
    (arity : ∀ ranges ∈ stages, ranges.length ≤ width) :
    (stages.map workBound).sum ≤ stages.length * width +
      sumMin stages * (1 + width * (2 + seekBudget maximum)) + delivered stages := by
  induction stages with
  | nil => simp [sumMin, delivered]
  | cons ranges rest ih =>
      have here := work_bound ranges maximum (bounded ranges (by simp))
      have size := arity ranges (by simp)
      have scale := Nat.mul_le_mul_left (minimumWidth ranges)
        (Nat.mul_le_mul_right (2 + seekBudget maximum) size)
      have later := ih (fun rs member => bounded rs (by simp [member]))
        (fun rs member => arity rs (by simp [member]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, sumMin, delivered] at *
      nlinarith

namespace Controls

def small : Range Nat := Range.ofArray #[2, 8] 0
def wide : Range Nat := Range.ofArray #[0, 1, 2, 3, 4, 5, 8, 9] 0
def other : Range Nat := Range.ofArray #[1, 2, 6, 8] 0

theorem chooses_smallest_not_first : selected [wide, small, other] = some small := by
  rfl

theorem three_way_exact : (intersect [wide, small, other]).map Result.keys = some [2, 8] := by
  simp only [intersect, chooses_smallest_not_first, Option.map_some]
  cbv

theorem membership_probe_retains_an_equal_boundary : (probe wide 2).1 = true := by cbv

theorem absent_key_not_nearest_key : (probe wide 7).1 = false := by cbv

theorem duplicate_range_is_not_a_bag_factor :
    ¬(Range.ofArray #[1, 1] 0).Sorted := by
  intro sorted
  have impossible := sorted 0 1 (by decide) (by decide) (by decide)
  contradiction

end Controls

end Mettapedia.Machines.Cursor.IndexedMultiwayProjection
