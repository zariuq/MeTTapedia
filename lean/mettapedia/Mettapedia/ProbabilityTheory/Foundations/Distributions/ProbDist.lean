import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# ProbDist: Finite Probability Distributions

A finite probability distribution on `Fin n` as a nonnegative vector summing to 1.
-/

namespace Mettapedia.ProbabilityTheory.Foundations.Distributions

open Finset
open scoped BigOperators

/-- A probability distribution over `Fin n` states. -/
structure ProbDist (n : ℕ) where
  p : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ p i
  sum_one : ∑ i, p i = 1

namespace ProbDist

variable {n : ℕ}

/-- Two distributions are equal if they agree on every coordinate. -/
@[ext] theorem ext (P Q : ProbDist n) (h : ∀ i, P.p i = Q.p i) : P = Q := by
  cases P with
  | mk pP nonnegP sumP =>
      cases Q with
      | mk pQ nonnegQ sumQ =>
          have hp : pP = pQ := by
            funext i
            exact h i
          cases hp
          have hnonneg : nonnegP = nonnegQ := by
            apply Subsingleton.elim
          have hsum : sumP = sumQ := by
            apply Subsingleton.elim
          cases hnonneg
          cases hsum
          rfl

/-- All probabilities are at most 1. -/
theorem le_one (P : ProbDist n) (i : Fin n) : P.p i ≤ 1 := by
  by_contra h
  push_neg at h
  have hsum : ∑ j, P.p j ≥ P.p i := single_le_sum (fun j _ => P.nonneg j) (mem_univ i)
  have : ∑ j, P.p j > 1 := lt_of_lt_of_le h hsum
  linarith [P.sum_one]

/-- Probability 1 at index i means all others are 0. -/
theorem eq_one_implies_others_zero (P : ProbDist n) (i : Fin n) (hi : P.p i = 1) :
    ∀ j, j ≠ i → P.p j = 0 := by
  intro j hj
  have hsum : ∑ k, P.p k = 1 := P.sum_one
  have hsplit : ∑ k, P.p k = P.p i + ∑ k ∈ univ.erase i, P.p k := by
    rw [add_comm, sum_erase_add _ _ (mem_univ i)]
  rw [hi] at hsplit
  have hrest : ∑ k ∈ univ.erase i, P.p k = 0 := by linarith [hsum, hsplit]
  have hnonneg : ∀ k ∈ univ.erase i, 0 ≤ P.p k := fun k _ => P.nonneg k
  have hzero := sum_eq_zero_iff_of_nonneg hnonneg
  rw [hzero] at hrest
  exact hrest j (mem_erase.mpr ⟨hj, mem_univ j⟩)

/-- The point-mass distribution concentrated at `i`. -/
noncomputable def pointMass {n : ℕ} (i : Fin n) : ProbDist n where
  p := fun j => if j = i then 1 else 0
  nonneg := by
    intro j
    by_cases h : j = i <;> simp [h]
  sum_one := by
    classical
    have hsingle :
        (∑ j : Fin n, (if j = i then (1 : ℝ) else 0)) = (if i = i then (1 : ℝ) else 0) := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j _ hji
        simp [hji]
      · intro hi
        simpa using (hi (Finset.mem_univ i))
    simp [hsingle]

@[simp] theorem pointMass_apply {n : ℕ} (i : Fin n) (j : Fin n) :
    (pointMass (n := n) i).p j = (if j = i then (1 : ℝ) else 0) := rfl

end ProbDist

end Mettapedia.ProbabilityTheory.Foundations.Distributions
