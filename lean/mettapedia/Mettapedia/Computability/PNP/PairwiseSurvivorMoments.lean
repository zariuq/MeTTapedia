import Mettapedia.Computability.PNP.FixedWidthIsolationObstruction
import Mathlib

open scoped BigOperators

/-!
# P vs NP crux: pairwise survivor moments imply small exact-isolation mass

This file packages the exact finite moment interface that pairwise-independent
hashing is supposed to provide for the survivor count:

* the first moment `E[Y] = μ`;
* the factorial second moment `E[Y(Y-1)] ≤ μ^2`.

From those, the variance budget `Var(Y) ≤ μ` follows, and therefore the exact
isolation probability is bounded by the fixed-width obstruction
`μ / (μ - 1)^2`.
-/

namespace Mettapedia.Computability.PNP

section

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

structure PairwiseSurvivorMomentModel where
  hitCount : Ω → ℕ
  mean : ℝ
  mean_eq :
    ∑ ω : Ω, (hitCount ω : ℝ) = Fintype.card Ω * mean
  factorialSecondMoment_le :
    ∑ ω : Ω, (hitCount ω : ℝ) * ((hitCount ω : ℝ) - 1)
      ≤ Fintype.card Ω * mean ^ 2

omit [DecidableEq Ω] in
theorem mean_nonneg (M : PairwiseSurvivorMomentModel (Ω := Ω)) :
    0 ≤ M.mean := by
  have hsum_nonneg : 0 ≤ ∑ ω : Ω, (M.hitCount ω : ℝ) := by
    exact Finset.sum_nonneg (fun ω _ => by positivity)
  have hΩ : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Ω›
  rw [M.mean_eq] at hsum_nonneg
  nlinarith

omit [DecidableEq Ω] in
theorem variance_budget
    (M : PairwiseSurvivorMomentModel (Ω := Ω)) :
    ∑ ω : Ω, (((M.hitCount ω : ℝ) - M.mean) ^ 2) ≤ Fintype.card Ω * M.mean := by
  have hsq_expand :
      ∑ ω : Ω, (((M.hitCount ω : ℝ) - M.mean) ^ 2)
        =
      ∑ ω : Ω, ((M.hitCount ω : ℝ) ^ 2)
        - 2 * M.mean * ∑ ω : Ω, (M.hitCount ω : ℝ)
        + Fintype.card Ω * M.mean ^ 2 := by
    calc
      ∑ ω : Ω, (((M.hitCount ω : ℝ) - M.mean) ^ 2)
        = ∑ ω : Ω,
            (((M.hitCount ω : ℝ) ^ 2)
              - 2 * M.mean * (M.hitCount ω : ℝ)
              + M.mean ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro ω hω
            ring
      _ = ∑ ω : Ω, ((M.hitCount ω : ℝ) ^ 2 - 2 * M.mean * (M.hitCount ω : ℝ))
            + ∑ ω : Ω, M.mean ^ 2 := by
            rw [Finset.sum_add_distrib]
      _ = (∑ ω : Ω, ((M.hitCount ω : ℝ) ^ 2))
            - ∑ ω : Ω, (2 * M.mean * (M.hitCount ω : ℝ))
            + ∑ ω : Ω, M.mean ^ 2 := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ ω : Ω, ((M.hitCount ω : ℝ) ^ 2))
            - 2 * M.mean * ∑ ω : Ω, (M.hitCount ω : ℝ)
            + Fintype.card Ω * M.mean ^ 2 := by
            rw [← Finset.mul_sum]
            simp
  have hsq_split :
      ∑ ω : Ω, ((M.hitCount ω : ℝ) ^ 2)
        =
      ∑ ω : Ω, (M.hitCount ω : ℝ) * ((M.hitCount ω : ℝ) - 1)
        + ∑ ω : Ω, (M.hitCount ω : ℝ) := by
    calc
      ∑ ω : Ω, ((M.hitCount ω : ℝ) ^ 2)
        = ∑ ω : Ω,
            ((M.hitCount ω : ℝ) * ((M.hitCount ω : ℝ) - 1)
              + (M.hitCount ω : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro ω hω
            ring
      _ = ∑ ω : Ω, (M.hitCount ω : ℝ) * ((M.hitCount ω : ℝ) - 1)
            + ∑ ω : Ω, (M.hitCount ω : ℝ) := by
            rw [Finset.sum_add_distrib]
  rw [hsq_expand, hsq_split]
  have hμ : 0 ≤ M.mean := mean_nonneg M
  have hstep :
      ∑ ω : Ω, (M.hitCount ω : ℝ) * ((M.hitCount ω : ℝ) - 1)
        + ∑ ω : Ω, (M.hitCount ω : ℝ)
        - 2 * M.mean * ∑ ω : Ω, (M.hitCount ω : ℝ)
        + Fintype.card Ω * M.mean ^ 2
        ≤
      Fintype.card Ω * M.mean ^ 2
        + Fintype.card Ω * M.mean
        - 2 * M.mean * (Fintype.card Ω * M.mean)
        + Fintype.card Ω * M.mean ^ 2 := by
    gcongr
    · exact M.factorialSecondMoment_le
    · exact M.mean_eq.le
    · exact M.mean_eq.ge
  have hΩ : 0 ≤ (Fintype.card Ω : ℝ) := by positivity
  nlinarith [hstep, M.mean_eq, hμ, hΩ]

omit [DecidableEq Ω] in
theorem exactOneProb_le
    (M : PairwiseSurvivorMomentModel (Ω := Ω))
    (hμ : 1 < M.mean) :
    exactOneProb M.hitCount ≤ M.mean / (M.mean - 1) ^ 2 := by
  exact exactOneProb_le_of_variance_budget M.hitCount M.mean hμ (variance_budget M)

end

end Mettapedia.Computability.PNP
