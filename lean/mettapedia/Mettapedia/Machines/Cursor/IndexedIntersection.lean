import Mettapedia.Machines.Cursor.OrderedIntersection
import Mettapedia.GSLT.Dynamics.RelationalKeyRanges

/-!
# Indexed realization of ordered key intersection

A range is an immutable random-access reader and two offsets. Its list view
is used only in the specification. Seeking changes an offset by binary
partition; it does not construct the skipped prefix. The operation ledger
counts midpoint comparisons separately from productive cursor advances.

The reader's access cost, index construction, lifetime and publication are
separate realization obligations. In particular, implementing `read` by a
linear list lookup does not have the constant-access cost used by this model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.IndexedIntersection

open Mettapedia.GSLT.Dynamics.RelationalKeyRanges
open OrderedIntersection

variable {Key : Type*} [LinearOrder Key]

structure Range (Key : Type*) where
  read : Nat → Key
  lo : Nat
  hi : Nat
  bounds : lo ≤ hi

def Range.width (r : Range Key) : Nat := r.hi - r.lo

def Range.view (r : Range Key) : List Key :=
  (List.range' r.lo r.width).map r.read

def Range.Sorted (r : Range Key) : Prop :=
  ∀ i j, r.lo ≤ i → i < j → j < r.hi → r.read i < r.read j

omit [LinearOrder Key] in
theorem view_length (r : Range Key) : r.view.length = r.width := by
  simp [Range.view]

omit [LinearOrder Key] in
theorem mem_view (r : Range Key) (key : Key) :
    key ∈ r.view ↔ ∃ i, r.lo ≤ i ∧ i < r.hi ∧ r.read i = key := by
  simp only [Range.view, List.mem_map, List.mem_range'_1]
  have extent : r.lo + r.width = r.hi := by have := r.bounds; dsimp [Range.width]; omega
  rw [extent]
  aesop

theorem view_sorted (r : Range Key) (sorted : r.Sorted) : r.view.Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj earlier
  simp only [Range.view, List.getElem_map, List.getElem_range', Nat.one_mul]
  apply sorted
  · omega
  · omega
  · rw [view_length] at hj
    dsimp [Range.width] at hj
    omega

def Range.tail (r : Range Key) : Range Key :=
  ⟨r.read, min (r.lo + 1) r.hi, r.hi, min_le_right _ _⟩

omit [LinearOrder Key] in
theorem tail_width (r : Range Key) : r.tail.width = r.width - 1 := by
  dsimp [Range.tail, Range.width]
  omega

omit [LinearOrder Key] in
theorem view_empty (r : Range Key) (empty : r.width = 0) : r.view = [] := by
  simp [Range.view, empty]

omit [LinearOrder Key] in
theorem view_cons (r : Range Key) (active : 0 < r.width) :
    r.view = r.read r.lo :: r.tail.view := by
  have size : r.width = (r.width - 1) + 1 := by omega
  have next : min (r.lo + 1) r.hi = r.lo + 1 := by
    dsimp [Range.width] at active
    omega
  unfold Range.view
  rw [size, List.range'_succ, List.map_cons]
  simp only [Range.tail, next]
  congr 2

theorem tail_sorted (r : Range Key) (sorted : r.Sorted) : r.tail.Sorted := by
  intro i j lo earlier hi
  exact sorted i j (by dsimp [Range.tail] at lo; have := r.bounds; omega) earlier hi

theorem partition_bounds (before : Nat → Bool) (lo hi : Nat) (bounds : lo ≤ hi) :
    lo ≤ (binaryPartition before lo hi).1 ∧ (binaryPartition before lo hi).1 ≤ hi := by
  induction width : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | h width ih =>
      rw [binaryPartition]
      split
      next active =>
        let mid := lo + (hi - lo) / 2
        have middle : lo ≤ mid ∧ mid < hi := by dsimp [mid]; omega
        change lo ≤ (if before mid then binaryPartition before (mid + 1) hi
          else binaryPartition before lo mid).1 ∧
          (if before mid then binaryPartition before (mid + 1) hi
          else binaryPartition before lo mid).1 ≤ hi
        split
        · have rest := ih (hi - (mid + 1)) (by omega) (mid + 1) hi (by omega) rfl
          omega
        · have rest := ih (mid - lo) (by omega) lo mid middle.1 rfl
          omega
      next empty => exact ⟨le_rfl, bounds⟩

def Range.seek (r : Range Key) (target : Key) : Range Key × Nat :=
  let result := binaryPartition (fun i => decide (r.read i < target)) r.lo r.hi
  (⟨r.read, result.1, r.hi,
    (partition_bounds (fun i => decide (r.read i < target)) r.lo r.hi r.bounds).2⟩,
   result.2)

theorem seek_width (r : Range Key) (target : Key) : (r.seek target).1.width ≤ r.width := by
  have bound := partition_bounds (fun i => decide (r.read i < target)) r.lo r.hi r.bounds
  dsimp [Range.seek, Range.width]
  omega

theorem seek_sorted (r : Range Key) (target : Key) (sorted : r.Sorted) :
    (r.seek target).1.Sorted := by
  have bound := partition_bounds (fun i => decide (r.read i < target)) r.lo r.hi r.bounds
  intro i j lo earlier hi
  exact sorted i j (by dsimp [Range.seek] at lo; omega) earlier hi

theorem seek_view (r : Range Key) (target : Key) (sorted : r.Sorted) :
    (r.seek target).1.view = seekTo target r.view := by
  have initial : InitialSegment (fun i => decide (r.read i < target)) r.lo r.hi := by
    intro i j lo ascending hi accepted
    simp only [decide_eq_true_eq] at accepted ⊢
    by_cases same : i = j
    · simpa [same] using accepted
    · exact (sorted i j lo (by omega) hi).trans accepted
  obtain ⟨lower, upper, before, after⟩ :=
    binaryPartition_correct _ r.lo r.hi initial r.bounds
  apply (view_sorted _ (seek_sorted r target sorted)).eq_of_mem_iff
    (OrderedIntersection.seek_sorted target r.view (view_sorted r sorted))
  intro key
  rw [OrderedIntersection.seek_membership target r.view (view_sorted r sorted),
    mem_view, mem_view]
  constructor
  · rintro ⟨i, lo, hi, same⟩
    change r.read i = key at same
    have notBefore := after i lo hi
    simp only [decide_eq_false_iff_not] at notBefore
    exact ⟨⟨i, lower.trans lo, hi, same⟩, by simpa [same] using le_of_not_gt notBefore⟩
  · rintro ⟨⟨i, lo, hi, same⟩, atLeast⟩
    refine ⟨i, ?_, hi, same⟩
    change (binaryPartition _ r.lo r.hi).1 ≤ i
    by_contra missed
    have tooSmall := before i lo (Nat.lt_of_not_ge missed)
    simp only [decide_eq_true_eq] at tooSmall
    exact (not_lt_of_ge atLeast) (by simpa [same] using tooSmall)

theorem seek_comparisons (r : Range Key) (target : Key) (k : Nat)
    (size : r.width < 2 ^ k) : (r.seek target).2 ≤ k :=
  binaryPartition_comparisons_le _ r.lo r.hi k r.bounds size

structure Result (Key : Type*) where
  keys : List Key
  advances : Nat
  comparisons : Nat
  deriving Repr, DecidableEq

def Result.erase (result : Result Key) : List Key × Nat := (result.keys, result.advances)

def Result.hit (key : Key) (result : Result Key) : Result Key :=
  ⟨key :: result.keys, result.advances + 1, result.comparisons⟩

def Result.skip (charge : Nat) (result : Result Key) : Result Key :=
  ⟨result.keys, result.advances + 1, result.comparisons + charge⟩

/-- Fuel bounds productive advances, not results. Exhaustion is an explicit
refusal, never an empty successful answer. The public entry supplies enough
fuel from the two ranges' widths. -/
def run : Nat → Range Key → Range Key → Option (Result Key)
  | fuel, first, second =>
    if first.width = 0 ∨ second.width = 0 then some ⟨[], 0, 0⟩
    else match fuel with
    | 0 => none
    | fuel + 1 =>
      let a := first.read first.lo
      let b := second.read second.lo
      if b < a then none
      else if a = b then (run fuel second first.tail).map (Result.hit a)
      else
        let sought := first.tail.seek b
        (run fuel second sought.1).map (Result.skip sought.2)

theorem run_refines (fuel : Nat) (first second : Range Key)
    (firstSorted : first.Sorted) (secondSorted : second.Sorted)
    (enough : first.width + second.width ≤ fuel) :
    (run fuel first second).map Result.erase = navigate first.view second.view := by
  induction fuel generalizing first second with
  | zero =>
      have empty : first.width = 0 := by omega
      simp [run, empty, view_empty first empty, navigate, Result.erase]
  | succ fuel ih =>
      by_cases leftEmpty : first.width = 0
      · simp [run, leftEmpty, view_empty first leftEmpty, navigate, Result.erase]
      by_cases rightEmpty : second.width = 0
      · rw [run, if_pos (Or.inr rightEmpty), view_empty second rightEmpty]
        cases first.view <;> simp [navigate, Result.erase]
      have leftActive : 0 < first.width := Nat.pos_of_ne_zero leftEmpty
      have rightActive : 0 < second.width := Nat.pos_of_ne_zero rightEmpty
      rw [run, if_neg (not_or.mpr ⟨leftEmpty, rightEmpty⟩),
        view_cons first leftActive, view_cons second rightActive, navigate]
      dsimp only
      split
      · rfl
      next notAhead =>
        split
        next same =>
          have smaller : second.width + first.tail.width ≤ fuel := by rw [tail_width]; omega
          have rest := ih second first.tail secondSorted (tail_sorted first firstSorted) smaller
          rw [← view_cons second rightActive, ← rest]
          cases run fuel second first.tail <;> rfl
        next different =>
          have smaller : second.width + (first.tail.seek (second.read second.lo)).1.width ≤ fuel := by
            have := seek_width first.tail (second.read second.lo)
            rw [tail_width] at this
            omega
          have rest := ih second (first.tail.seek (second.read second.lo)).1 secondSorted
            (seek_sorted first.tail _ (tail_sorted first firstSorted)) smaller
          rw [seek_view first.tail _ (tail_sorted first firstSorted)] at rest
          rw [← view_cons second rightActive, ← rest]
          cases run fuel second (first.tail.seek (second.read second.lo)).1 <;> rfl

/-- The charged comparisons belong to the same binary-seeking execution
whose erasure refines the independent list navigation. -/
theorem run_comparisons (fuel : Nat) (first second : Range Key) (k : Nat)
    (leftSize : first.width < 2 ^ k) (rightSize : second.width < 2 ^ k)
    (result : Result Key) (completed : run fuel first second = some result) :
    result.comparisons ≤ result.advances * k := by
  induction fuel generalizing first second result with
  | zero =>
      simp only [run] at completed
      split at completed
      · cases Option.some.inj completed
        simp
      · cases completed
  | succ fuel ih =>
      rw [run] at completed
      split at completed
      · cases Option.some.inj completed
        simp
      next active =>
        dsimp only at completed
        split at completed
        · cases completed
        next notAhead =>
          split at completed
          next same =>
            obtain ⟨rest, runRest, rfl⟩ := Option.map_eq_some_iff.mp completed
            have tailSize : first.tail.width < 2 ^ k := by rw [tail_width]; omega
            have restBound := ih second first.tail rightSize tailSize rest runRest
            dsimp [Result.hit]
            nlinarith
          next different =>
            obtain ⟨rest, runRest, rfl⟩ := Option.map_eq_some_iff.mp completed
            have tailSize : first.tail.width < 2 ^ k := by rw [tail_width]; omega
            have soughtSize := lt_of_le_of_lt (seek_width first.tail (second.read second.lo)) tailSize
            have restBound := ih second (first.tail.seek (second.read second.lo)).1
              rightSize soughtSize rest runRest
            have charge := seek_comparisons first.tail (second.read second.lo) k tailSize
            dsimp [Result.skip]
            nlinarith

def intersection (first second : Range Key) : Option (Result Key) :=
  if first.width = 0 ∨ second.width = 0 then some ⟨[], 0, 0⟩
  else if second.read second.lo < first.read first.lo then
    run (first.width + second.width) second first
  else run (first.width + second.width) first second

theorem intersection_refines (first second : Range Key)
    (firstSorted : first.Sorted) (secondSorted : second.Sorted) :
    (intersection first second).map Result.erase =
      OrderedIntersection.intersection first.view second.view := by
  by_cases leftEmpty : first.width = 0
  · rw [intersection, if_pos (Or.inl leftEmpty), view_empty first leftEmpty]
    cases second.view <;> simp [OrderedIntersection.intersection, navigate, Result.erase]
  by_cases rightEmpty : second.width = 0
  · rw [intersection, if_pos (Or.inr rightEmpty), view_empty second rightEmpty]
    cases first.view <;> simp [OrderedIntersection.intersection, navigate, Result.erase]
  have firstShape := view_cons first (Nat.pos_of_ne_zero leftEmpty)
  have secondShape := view_cons second (Nat.pos_of_ne_zero rightEmpty)
  rw [intersection, if_neg (not_or.mpr ⟨leftEmpty, rightEmpty⟩)]
  split
  · rw [run_refines _ _ _ secondSorted firstSorted (by omega), firstShape, secondShape]
    simp_all only [OrderedIntersection.intersection, ↓reduceIte]
  · rw [run_refines _ _ _ firstSorted secondSorted le_rfl, firstShape, secondShape]
    simp_all only [OrderedIntersection.intersection, ↓reduceIte]

/-- Existence, exact ordered support, the sum-min advance bound and the
logarithmic midpoint ledger all hold for one concrete indexed worker. -/
theorem intersection_spec (first second : Range Key)
    (firstSorted : first.Sorted) (secondSorted : second.Sorted)
    (k : Nat) (leftSize : first.width < 2 ^ k) (rightSize : second.width < 2 ^ k) :
    ∃ result, intersection first second = some result ∧
      (∀ key, key ∈ result.keys ↔ key ∈ first.view ∧ key ∈ second.view) ∧
      result.keys.Pairwise (· < ·) ∧
      result.advances ≤ 2 * min first.width second.width ∧
      result.comparisons ≤ result.advances * k := by
  obtain ⟨keys, advances, runReference, members, sorted, bound⟩ :=
    OrderedIntersection.intersection_spec first.view second.view
      (view_sorted first firstSorted) (view_sorted second secondSorted)
  have erased := intersection_refines first second firstSorted secondSorted
  rw [runReference] at erased
  obtain ⟨result, completed, same⟩ := Option.map_eq_some_iff.mp erased
  have sameKeys : result.keys = keys := congrArg Prod.fst same
  have sameAdvances : result.advances = advances := congrArg Prod.snd same
  refine ⟨result, completed, by simpa [sameKeys] using members,
    by simpa [sameKeys] using sorted, ?_, ?_⟩
  · simpa [sameAdvances, view_length] using bound
  · unfold intersection at completed
    split at completed
    · cases Option.some.inj completed
      simp
    · split at completed
      · exact run_comparisons _ second first k rightSize leftSize result completed
      · exact run_comparisons _ first second k leftSize rightSize result completed

/-- The standard logarithmic budget also covers empty ranges. -/
def seekBudget (maximum : Nat) : Nat := Nat.log 2 maximum + 1

omit [LinearOrder Key] in
theorem width_lt_budget (r : Range Key) (maximum : Nat) (bounded : r.width ≤ maximum) :
    r.width < 2 ^ seekBudget maximum :=
  bounded.trans_lt (Nat.lt_pow_succ_log_self (by decide) maximum)

/-- Two head comparisons per productive advance, binary comparisons, one
initial ordering comparison, and one delivery event per emitted key. -/
def Result.workBound (result : Result Key) : Nat :=
  1 + 2 * result.advances + result.comparisons + result.keys.length

theorem intersection_logarithmic_bound (first second : Range Key)
    (firstSorted : first.Sorted) (secondSorted : second.Sorted)
    (maximum : Nat) (leftBound : first.width ≤ maximum) (rightBound : second.width ≤ maximum) :
    ∃ result, intersection first second = some result ∧
      result.keys.toFinset = first.view.toFinset ∩ second.view.toFinset ∧
      result.workBound ≤
        1 + 2 * min first.width second.width * (2 + seekBudget maximum) + result.keys.length := by
  obtain ⟨result, completed, members, _, advances, comparisons⟩ :=
    intersection_spec first second firstSorted secondSorted (seekBudget maximum)
      (width_lt_budget first maximum leftBound) (width_lt_budget second maximum rightBound)
  refine ⟨result, completed, ?_, ?_⟩
  · ext key
    simpa only [List.mem_toFinset, Finset.mem_inter] using members key
  · dsimp [Result.workBound]
    have scaled := Nat.mul_le_mul_right (2 + seekBudget maximum) advances
    nlinarith

/-- A concrete random-access carrier. Values outside the range are irrelevant:
the worker only dereferences a nonempty range or a midpoint inside it. -/
def Range.ofArray (values : Array Key) (outside : Key) : Range Key :=
  ⟨fun i => values[i]?.getD outside, 0, values.size, Nat.zero_le _⟩

omit [LinearOrder Key] in
theorem ofArray_view (values : Array Key) (outside : Key) :
    (Range.ofArray values outside).view = values.toList := by
  apply List.ext_getElem
  · simp [Range.view, Range.ofArray, Range.width]
  · intro i left right
    simp [Range.view, Range.ofArray, Range.width, Array.getElem?_eq_getElem right]

theorem ofArray_sorted (values : Array Key) (outside : Key)
    (sorted : values.toList.Pairwise (· < ·)) : (Range.ofArray values outside).Sorted := by
  intro i j lo earlier hi
  have hi' : i < values.toList.length := by dsimp [Range.ofArray] at hi; simp; omega
  have hj' : j < values.toList.length := hi
  have order := List.pairwise_iff_getElem.mp sorted i j hi' hj' earlier
  simpa [Range.ofArray, Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hj'] using order

namespace Controls

def left : Range Nat := Range.ofArray #[0, 2, 4, 8] 0
def right : Range Nat := Range.ofArray #[1, 2, 3, 8, 9] 0

theorem sparse_binary_intersection :
    (intersection left right).map Result.erase = some ([2, 8], 7) := by
  rw [intersection_refines left right
    (ofArray_sorted _ _ (by decide)) (ofArray_sorted _ _ (by decide))]
  simpa [left, right, ofArray_view, OrderedIntersection.intersection] using
    OrderedIntersection.sparse_intersection

theorem no_fuel_is_not_absence : run 0 left right = none := by decide

theorem empty_is_success :
    intersection (Range.ofArray (#[] : Array Nat) 0) right = some ⟨[], 0, 0⟩ := by decide

theorem unordered_range_really_loses_a_key :
    (intersection (Range.ofArray #[0, 3, 1] 0) (Range.ofArray #[1] 0)).map Result.erase =
      some ([], 2) := by
  cbv

theorem unordered_not_admitted : ¬(Range.ofArray #[0, 3, 1] 0).Sorted := by
  intro sorted
  have impossible := sorted 1 2 (by decide) (by decide) (by decide)
  contradiction

end Controls

end Mettapedia.Machines.Cursor.IndexedIntersection
