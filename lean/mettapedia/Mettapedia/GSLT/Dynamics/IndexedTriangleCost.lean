import Mettapedia.GSLT.Dynamics.TriangleNavigationCost
import Mettapedia.Machines.Cursor.IndexedIntersection

/-!
# Binary-seeking triangle navigation

The executable indexed intersection supplies both its own progress trace and
its midpoint-comparison ledger. Summing these concrete results over admitted
two-coordinate prefixes connects the degree account to a logarithmic seek
cost. The support-triangle bound does not bound duplicate derivation output.
Parent-prefix generation, range preparation and leaf weights remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.IndexedTriangleCost

open Mettapedia.Machines.Cursor.IndexedIntersection
open RelationalCardinality

variable {Key X Y : Type*} [LinearOrder Key]

def result (first second : Range Key) : Result Key :=
  (intersection first second).getD ⟨[], 0, 0⟩

theorem result_spec (first second : Range Key)
    (firstSorted : first.Sorted) (secondSorted : second.Sorted)
    (maximum : Nat) (leftBound : first.width ≤ maximum) (rightBound : second.width ≤ maximum) :
    intersection first second = some (result first second) ∧
      (∀ key, key ∈ (result first second).keys ↔ key ∈ first.view ∧ key ∈ second.view) ∧
      (result first second).keys.Pairwise (· < ·) ∧
      (result first second).advances ≤ 2 * min first.width second.width ∧
      (result first second).comparisons ≤ (result first second).advances * seekBudget maximum := by
  obtain ⟨computed, done, exactKeys, ordered, advances, comparisons⟩ :=
    intersection_spec first second firstSorted secondSorted (seekBudget maximum)
      (width_lt_budget first maximum leftBound) (width_lt_budget second maximum rightBound)
  simpa only [result, done, Option.getD_some] using
    And.intro done (And.intro exactKeys (And.intro ordered (And.intro advances comparisons)))

theorem total_comparisons_bound (r : Finset (X × Y)) (s : Y → Range Key) (t : X → Range Key)
    (sSorted : ∀ pair ∈ r, (s pair.2).Sorted) (tSorted : ∀ pair ∈ r, (t pair.1).Sorted)
    (maximum : Nat) (sBound : ∀ pair ∈ r, (s pair.2).width ≤ maximum)
    (tBound : ∀ pair ∈ r, (t pair.1).width ≤ maximum) :
    (∑ pair ∈ r, (result (s pair.2) (t pair.1)).comparisons) ≤
      2 * triangleIntersectionWork r (fun y => (s y).width) (fun x => (t x).width) *
        seekBudget maximum := by
  calc
    _ ≤ ∑ pair ∈ r, 2 * min (s pair.2).width (t pair.1).width * seekBudget maximum := by
      apply Finset.sum_le_sum
      intro pair member
      have spec := result_spec (s pair.2) (t pair.1) (sSorted pair member) (tSorted pair member)
        maximum (sBound pair member) (tBound pair member)
      exact spec.2.2.2.2.trans (Nat.mul_le_mul_right _ spec.2.2.2.1)
    _ = _ := by simp [triangleIntersectionWork, Finset.sum_mul, Finset.mul_sum]

theorem total_comparisons_squared_bound [DecidableEq X] [DecidableEq Y]
    (r : Finset (X × Y)) (xs : Finset X) (ys : Finset Y) (covered : r ⊆ xs ×ˢ ys)
    (s : Y → Range Key) (t : X → Range Key)
    (sSorted : ∀ pair ∈ r, (s pair.2).Sorted) (tSorted : ∀ pair ∈ r, (t pair.1).Sorted)
    (maximum : Nat) (sBound : ∀ pair ∈ r, (s pair.2).width ≤ maximum)
    (tBound : ∀ pair ∈ r, (t pair.1).width ≤ maximum) :
    (∑ pair ∈ r, (result (s pair.2) (t pair.1)).comparisons) ^ 2 ≤
      4 * (r.card * (∑ x ∈ xs, (t x).width) * (∑ y ∈ ys, (s y).width)) *
        seekBudget maximum ^ 2 := by
  have navigation := total_comparisons_bound r s t sSorted tSorted maximum sBound tBound
  have degrees := triangle_intersection_work_sq_le r xs ys covered
    (fun y => (s y).width) (fun x => (t x).width)
  calc
    _ ≤ (2 * triangleIntersectionWork r (fun y => (s y).width) (fun x => (t x).width) *
        seekBudget maximum) ^ 2 := pow_le_pow_left' navigation 2
    _ = 4 * triangleIntersectionWork r (fun y => (s y).width) (fun x => (t x).width) ^ 2 *
        seekBudget maximum ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 degrees)

theorem support_output_exact (r : Finset (X × Y)) (s : Y → Range Key) (t : X → Range Key)
    (sSorted : ∀ pair ∈ r, (s pair.2).Sorted) (tSorted : ∀ pair ∈ r, (t pair.1).Sorted) :
    (∑ pair ∈ r, (result (s pair.2) (t pair.1)).keys.length) =
      triangleCount r (fun y => (s y).view.toFinset) (fun x => (t x).view.toFinset) := by
  apply Finset.sum_congr rfl
  intro pair member
  have spec := result_spec (s pair.2) (t pair.1) (sSorted pair member) (tSorted pair member)
    (max (s pair.2).width (t pair.1).width) (le_max_left _ _) (le_max_right _ _)
  have same : (result (s pair.2) (t pair.1)).keys.toFinset =
      (s pair.2).view.toFinset ∩ (t pair.1).view.toFinset := by
    ext key
    simpa only [List.mem_toFinset, Finset.mem_inter] using spec.2.1 key
  rw [← same]
  exact (List.toFinset_card_of_nodup spec.2.2.1.nodup).symm

/-- One support triangle can carry eight physical occurrence triples. -/
theorem support_work_is_not_bag_output :
    leafMultiplicity ([[0, 0], [0, 0], [0, 0]] : List (List Nat)) = 8 ∧
      triangleCount ({(0, 0)} : Finset (Nat × Nat)) (fun _ => {0}) (fun _ => {0}) = 1 := by decide

end Mettapedia.GSLT.Dynamics.IndexedTriangleCost
