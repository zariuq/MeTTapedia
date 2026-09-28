import Mettapedia.ProbabilityTheory.IndependentFiniteSampling

/-!
# Coordinatewise pushforward of a finite independent sample

Private coordinate transformations commute with the product construction.
This connects a law stated directly on final states to a realization that
first samples per-identity inputs and then transforms each private state.
The proof compares every output probability by finite sum/product expansion.
-/

namespace Mettapedia.ProbabilityTheory.IndependentFiniteSampling

open scoped BigOperators

variable {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

/-- Mapping each private coordinate after drawing the input product law is
the same joint distribution as the product of the mapped coordinate laws. -/
theorem independent_map (p : I → PMF A) (f : I → A → B) :
    (independent p).map (fun xs i => f i (xs i)) =
      independent (fun i => (p i).map (f i)) := by
  classical
  ext ys
  simp only [PMF.map_apply, independent_apply, tsum_fintype]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro xs _
  by_cases equal : ys = fun i => f i (xs i)
  · subst ys
    simp
  · rw [if_neg equal]
    obtain ⟨i, different⟩ : ∃ i, ys i ≠ f i (xs i) := by
      by_contra none
      push Not at none
      exact equal (funext none)
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg different)

end Mettapedia.ProbabilityTheory.IndependentFiniteSampling
