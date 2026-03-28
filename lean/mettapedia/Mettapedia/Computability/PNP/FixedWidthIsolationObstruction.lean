import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

/-!
# P vs NP crux: fixed-width hashing cannot isolate large solution sets often

The manuscript fixes the VV hash width at `k = c_1 log m`, but the classical
Valiant-Vazirani isolation probability `Omega(1/m)` comes from averaging over
many scales of `k`.

This file formalizes the finite counting obstruction behind that mismatch. If the
retained-candidate count `Y` under a random hash has mean `μ > 1` and variance
at most `μ`, then the exact-isolation event `Y = 1` can occur only on a
`μ / (μ - 1)^2` fraction of the hash space, which is `O(1/μ)`.
-/

namespace Mettapedia.Computability.PNP

section

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- Hash choices that leave exactly one surviving candidate. -/
def exactOneSet (Y : Ω → ℕ) : Finset Ω :=
  Finset.univ.filter fun ω => Y ω = 1

/-- Finite-space exact-isolation probability, represented as a real ratio. -/
noncomputable def exactOneProb (Y : Ω → ℕ) : ℝ :=
  (exactOneSet Y).card / Fintype.card Ω

omit [DecidableEq Ω] in
theorem exactOneProb_le_of_variance_budget
    (Y : Ω → ℕ)
    (μ : ℝ)
    (hμ : 1 < μ)
    (hvar : ∑ ω : Ω, (((Y ω : ℝ) - μ) ^ 2) ≤ Fintype.card Ω * μ) :
    exactOneProb Y ≤ μ / (μ - 1) ^ 2 := by
  have hterm :
      ∀ ω ∈ exactOneSet Y, (μ - 1) ^ 2 ≤ (((Y ω : ℝ) - μ) ^ 2) := by
    intro ω hω
    have hY : (Y ω : ℝ) = 1 := by
      simp [exactOneSet] at hω
      exact_mod_cast hω
    rw [hY]
    nlinarith
  have hsum_filter :
      Finset.sum (exactOneSet Y) (fun _ : Ω => (μ - 1) ^ 2)
        ≤ Finset.sum (exactOneSet Y) (fun ω : Ω => (((Y ω : ℝ) - μ) ^ 2)) := by
    exact Finset.sum_le_sum (fun ω hω => hterm ω hω)
  have hsum_filter_card :
      ((exactOneSet Y).card : ℝ) * (μ - 1) ^ 2
        ≤ Finset.sum (exactOneSet Y) (fun ω : Ω => (((Y ω : ℝ) - μ) ^ 2)) := by
    simpa using hsum_filter
  have hsum_le_total :
      Finset.sum (exactOneSet Y) (fun ω : Ω => (((Y ω : ℝ) - μ) ^ 2))
        ≤ ∑ ω : Ω, (((Y ω : ℝ) - μ) ^ 2) := by
    simpa [exactOneSet] using
      (Finset.sum_le_univ_sum_of_nonneg (f := fun ω : Ω => (((Y ω : ℝ) - μ) ^ 2))
        (fun ω => sq_nonneg ((Y ω : ℝ) - μ)))
  have hmain :
      ((exactOneSet Y).card : ℝ) * (μ - 1) ^ 2 ≤ Fintype.card Ω * μ := by
    exact le_trans hsum_filter_card (le_trans hsum_le_total hvar)
  have hΩ : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Ω›
  have hden : 0 < (μ - 1) ^ 2 := by
    nlinarith [hμ]
  have hmain' :
      ((exactOneSet Y).card : ℝ) * (μ - 1) ^ 2 ≤ Fintype.card Ω * μ := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  have hcount :
      ((exactOneSet Y).card : ℝ) ≤ Fintype.card Ω * (μ / (μ - 1) ^ 2) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((le_div_iff₀ hden).2 hmain')
  have hgoal :
      ((exactOneSet Y).card : ℝ) / Fintype.card Ω ≤ μ / (μ - 1) ^ 2 := by
    exact (div_le_iff₀ hΩ).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcount)
  simpa [exactOneProb] using hgoal

end

end Mettapedia.Computability.PNP
