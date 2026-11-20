import Mettapedia.PLN.TruthValues.PLNTruthTower
import Mettapedia.InformationTheory.PredictiveLogLoss

/-!
# Binary evidence as a log-likelihood statistic

The strength of an observed Bernoulli row is its maximum-likelihood
parameter. Posterior expectations of complete-data outcomes yield the
same count statistic with real weights. These weights are relative to the
E-step snapshot and are recomputed on the next E-step.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV

noncomputable def bernoulli (p : ℝ) (nonneg : 0 ≤ p) (bounded : p ≤ 1) : Prob Bool :=
  ⟨fun b => if b then p else 1 - p,
    fun b => by cases b <;> simp [nonneg, sub_nonneg.mpr bounded], by simp⟩

noncomputable def empirical (counts : BinaryCounts) (nonempty : counts.total ≠ 0) : Prob Bool :=
  bernoulli counts.strength (counts.strength_nonneg_of_total_ne_zero nonempty)
    (counts.strength_le_one_of_total_ne_zero nonempty)

@[simp] theorem empirical_apply_true (counts : BinaryCounts) (nonempty : counts.total ≠ 0) :
    (counts.empirical nonempty).1 true = counts.nPlus / counts.total := rfl

@[simp] theorem empirical_apply_false (counts : BinaryCounts) (nonempty : counts.total ≠ 0) :
    (counts.empirical nonempty).1 false = counts.nMinus / counts.total := by
  change 1 - counts.nPlus / counts.total = counts.nMinus / counts.total
  field_simp
  simp [total]

/-- Negative log likelihood in nats. Its finite interpretation requires
positive forecast mass wherever the corresponding count is positive. -/
noncomputable def logLoss (counts : BinaryCounts) (parameter : ℝ) : ℝ :=
  counts.nPlus * (-Real.log parameter) + counts.nMinus * (-Real.log (1 - parameter))

theorem logLoss_eq_scaled_crossEntropy (counts : BinaryCounts) (nonempty : counts.total ≠ 0)
    (p : ℝ) (nonneg : 0 ≤ p) (bounded : p ≤ 1) :
    counts.logLoss p = counts.total * crossEntropy (counts.empirical nonempty)
      (bernoulli p nonneg bounded) := by
  have den : counts.nPlus + counts.nMinus ≠ 0 := nonempty
  simp [logLoss, crossEntropy, bernoulli]
  field_simp
  ring

/-- The excess log loss of a candidate row uses the same count scale as
the evidence ledger. An empty ledger does not identify a parameter. -/
theorem logLoss_gap_eq_kl (counts : BinaryCounts) (nonempty : counts.total ≠ 0)
    (p : ℝ) (nonneg : 0 ≤ p) (bounded : p ≤ 1)
    (support : ∀ b, 0 < (counts.empirical nonempty).1 b →
      0 < (bernoulli p nonneg bounded).1 b) :
    counts.logLoss p - counts.logLoss counts.mleStrength =
      counts.total * klSum (counts.empirical nonempty).1 (bernoulli p nonneg bounded).1 := by
  rw [mleStrength_eq_strength, counts.logLoss_eq_scaled_crossEntropy nonempty _ nonneg bounded,
    counts.logLoss_eq_scaled_crossEntropy nonempty _
      (counts.strength_nonneg_of_total_ne_zero nonempty)
      (counts.strength_le_one_of_total_ne_zero nonempty),
    crossEntropy_eq_entropy_add_kl _ _ support]
  change counts.total * (shannonEntropyFin Bool (counts.empirical nonempty) + _) -
    counts.total * crossEntropy (counts.empirical nonempty) (counts.empirical nonempty) = _
  rw [crossEntropy_self]
  ring

theorem mle_minimizes_logLoss (counts : BinaryCounts) (nonempty : counts.total ≠ 0)
    (p : ℝ) (nonneg : 0 ≤ p) (bounded : p ≤ 1)
    (support : ∀ b, 0 < (counts.empirical nonempty).1 b →
      0 < (bernoulli p nonneg bounded).1 b) :
    counts.logLoss counts.mleStrength ≤ counts.logLoss p := by
  rw [mleStrength_eq_strength, counts.logLoss_eq_scaled_crossEntropy nonempty _ nonneg bounded,
    counts.logLoss_eq_scaled_crossEntropy nonempty _
      (counts.strength_nonneg_of_total_ne_zero nonempty)
      (counts.strength_le_one_of_total_ne_zero nonempty)]
  exact mul_le_mul_of_nonneg_left (crossEntropy_min _ _ support) counts.total_nonneg

section Expected

variable {I S : Type*} [Fintype I] [Fintype S]

/-- A complete world may contribute to either outcome of an active row.
`none` means the parent configuration for that row was absent. -/
noncomputable def expected (posterior : I → Prob S) (outcome : I → S → Option Bool) :
    BinaryCounts where
  nPlus := ∑ i, ∑ s, if outcome i s = some true then (posterior i).1 s else 0
  nMinus := ∑ i, ∑ s, if outcome i s = some false then (posterior i).1 s else 0
  nPlus_nonneg := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ => by
    split
    · exact (posterior i).2.1 s
    · exact le_rfl
  nMinus_nonneg := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ => by
    split
    · exact (posterior i).2.1 s
    · exact le_rfl

/-- A Bernoulli row's contribution to the expected negative complete-data
log likelihood reduces to two posterior-weighted counts. -/
theorem expected_logLoss (posterior : I → Prob S) (outcome : I → S → Option Bool) (p : ℝ) :
    (expected posterior outcome).logLoss p =
      ∑ i, ∑ s, (posterior i).1 s *
        (match outcome i s with
          | some true => -Real.log p
          | some false => -Real.log (1 - p)
          | none => 0) := by
  simp only [expected, logLoss, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro s _
  cases outcome i s with
  | none => simp
  | some observed => cases observed <;> simp

end Expected
end Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts
