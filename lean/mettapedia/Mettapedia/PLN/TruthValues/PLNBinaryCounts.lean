import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
import Mettapedia.PLN.TruthValues.PLNConfidenceWeight

/-! Finite binary counts and their strength and confidence projections. -/

namespace Mettapedia.PLN.TruthValues.PLNTruthTower

open scoped ENNReal NNReal
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate

/-! ## Evidence counts: the load-bearing binary state -/

/-- Finite binary evidence counts, with positivity carried explicitly.

The zero-total case is allowed at this layer.  Views that divide by total
evidence ask separately for `total ≠ 0`. -/
structure BinaryCounts where
  nPlus : ℝ
  nMinus : ℝ
  nPlus_nonneg : 0 ≤ nPlus
  nMinus_nonneg : 0 ≤ nMinus

namespace BinaryCounts

/-- Total finite evidence count. -/
noncomputable def total (e : BinaryCounts) : ℝ := e.nPlus + e.nMinus

@[simp] theorem total_eq (e : BinaryCounts) : e.total = e.nPlus + e.nMinus := rfl

/-- Total evidence is nonnegative. -/
theorem total_nonneg (e : BinaryCounts) : 0 ≤ e.total := by
  simp [total, add_nonneg e.nPlus_nonneg e.nMinus_nonneg]

/-- The strength coordinate determined by positive finite total evidence. -/
noncomputable def strength (e : BinaryCounts) : ℝ := e.nPlus / e.total

/-- Nonzero finite binary evidence has strictly positive total weight. -/
theorem total_pos_of_ne_zero (e : BinaryCounts) (hTotal : e.total ≠ 0) :
    0 < e.total := by
  exact lt_of_le_of_ne e.total_nonneg hTotal.symm

/-- Positive-total binary evidence displays a nonnegative strength. -/
theorem strength_nonneg_of_total_ne_zero
    (e : BinaryCounts) (_hTotal : e.total ≠ 0) :
    0 ≤ e.strength := by
  unfold strength
  exact div_nonneg e.nPlus_nonneg e.total_nonneg

/-- Positive-total binary evidence displays strength at most one. -/
theorem strength_le_one_of_total_ne_zero
    (e : BinaryCounts) (hTotal : e.total ≠ 0) :
    e.strength ≤ 1 := by
  have hPos : 0 < e.total := e.total_pos_of_ne_zero hTotal
  unfold strength
  rw [div_le_one hPos]
  exact le_add_of_nonneg_right e.nMinus_nonneg

/-- Positive-total binary evidence displays a unit-interval strength. -/
theorem strength_mem_unit_of_total_ne_zero
    (e : BinaryCounts) (hTotal : e.total ≠ 0) :
    e.strength ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨e.strength_nonneg_of_total_ne_zero hTotal,
    e.strength_le_one_of_total_ne_zero hTotal⟩

/-- The maximum-likelihood / improper-prior strength projection.  This is the
standard PLN simple strength view of the counts. -/
noncomputable def mleStrength (e : BinaryCounts) : ℝ := e.strength

@[simp] theorem mleStrength_eq_strength (e : BinaryCounts) :
    e.mleStrength = e.strength :=
  rfl

/-- Denominator for the Beta-posterior mean projection determined by a binary
prior context. -/
noncomputable def posteriorDenom
    (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
    (e : BinaryCounts) : ℝ :=
  ctx.α₀.toReal + ctx.β₀.toReal + e.total

/-- Contextual Beta-posterior mean strength projection.  Unlike PLN simple
strength, this projection makes the prior/context degree of freedom explicit. -/
noncomputable def posteriorMeanStrength
    (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
    (e : BinaryCounts) : ℝ :=
  (ctx.α₀.toReal + e.nPlus) / posteriorDenom ctx e

/-- The posterior denominator is always nonnegative. -/
theorem posteriorDenom_nonneg
    (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
    (e : BinaryCounts) :
    0 ≤ posteriorDenom ctx e := by
  exact add_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) e.total_nonneg

/-- The contextual posterior-mean strength is a unit interval value whenever
its denominator is genuinely positive. -/
theorem posteriorMeanStrength_in_unit_of_pos_denom
    (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
    (e : BinaryCounts)
    (hden : 0 < posteriorDenom ctx e) :
    0 ≤ posteriorMeanStrength ctx e ∧ posteriorMeanStrength ctx e ≤ 1 := by
  unfold posteriorMeanStrength
  constructor
  · apply div_nonneg
    · exact add_nonneg ENNReal.toReal_nonneg e.nPlus_nonneg
    · exact le_of_lt hden
  · apply (div_le_one hden).2
    unfold posteriorDenom
    have hβ : 0 ≤ ctx.β₀.toReal := ENNReal.toReal_nonneg
    linarith [hβ, e.nMinus_nonneg, e.total_eq]

/-- PLN simple strength is the Beta posterior-mean projection with the
improper/Haldane prior context. -/
@[simp] theorem posteriorMeanStrength_improper_eq_mle
    (e : BinaryCounts) :
    posteriorMeanStrength Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.improper e =
      e.mleStrength := by
  simp [posteriorMeanStrength, posteriorDenom, mleStrength, strength,
    total, Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.improper]

/-- A one-positive-observation count state for projection canaries. -/
def singlePositive : BinaryCounts where
  nPlus := 1
  nMinus := 0
  nPlus_nonneg := by norm_num
  nMinus_nonneg := by norm_num

/-- Prior/context choice is a real degree of freedom: the same retained counts
display as strength `1` under the improper/MLE projection and `2/3` under the
uniform Beta-posterior mean projection. -/
theorem singlePositive_uniform_prior_changes_strength :
    singlePositive.mleStrength = 1 ∧
      posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform singlePositive =
        (2 / 3 : ℝ) ∧
        singlePositive.mleStrength ≠
          posteriorMeanStrength
            Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform singlePositive := by
  norm_num [singlePositive, mleStrength, strength, posteriorMeanStrength,
    posteriorDenom, total, Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform]

/-- Embed finite natural-number evidence counts into the real-valued tower
state. -/
def ofNatCounts (nPos nNeg : ℕ) : BinaryCounts where
  nPlus := nPos
  nMinus := nNeg
  nPlus_nonneg := by exact_mod_cast (Nat.zero_le nPos)
  nMinus_nonneg := by exact_mod_cast (Nat.zero_le nNeg)

@[simp] theorem ofNatCounts_total (nPos nNeg : ℕ) :
    (ofNatCounts nPos nNeg).total = nPos + nNeg := by
  simp [ofNatCounts, total]

/-- The real-valued MLE/improper projection agrees with the existing
Nat-count Haldane/PLN strength ledger. -/
theorem ofNatCounts_mleStrength_eq_predHaldane
    (nPos nNeg : ℕ) :
    (ofNatCounts nPos nNeg).mleStrength =
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predHaldane nPos nNeg := by
  by_cases h : nPos + nNeg = 0
  · have hPos : nPos = 0 := Nat.eq_zero_of_add_eq_zero_right h
    have hNeg : nNeg = 0 := Nat.eq_zero_of_add_eq_zero_left h
    simp [ofNatCounts, mleStrength, strength, total,
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predHaldane,
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.plnStrength,
      Mettapedia.PLN.Evidence.EvidenceCounts.plnStrength, hPos, hNeg]
  · have hTower :
        (ofNatCounts nPos nNeg).mleStrength =
          (nPos : ℝ) / ((nPos + nNeg : ℕ) : ℝ) := by
      simp [ofNatCounts, mleStrength, strength, total, Nat.cast_add]
    have hLedger :
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predHaldane nPos nNeg =
          (nPos : ℝ) / ((nPos + nNeg : ℕ) : ℝ) := by
      simpa [Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predHaldane] using
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.plnStrength_eq_improper_mean nPos nNeg h
    rw [hTower, hLedger]

/-- The real-valued uniform-prior projection agrees with the existing
Nat-count Laplace/uniform posterior-mean ledger. -/
theorem ofNatCounts_uniformPosterior_eq_predLaplace
    (nPos nNeg : ℕ) :
    posteriorMeanStrength
        Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
        (ofNatCounts nPos nNeg) =
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predLaplace nPos nNeg := by
  simp [posteriorMeanStrength, posteriorDenom, ofNatCounts, total,
    Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform,
    Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predLaplace,
    Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.uniformPosteriorMean,
    Mettapedia.PLN.Evidence.EvidenceCounts.uniformPosteriorMean]
  ring_nf

/-- The real-valued Jeffreys-prior projection agrees with the existing
Nat-count Jeffreys/KT posterior-mean ledger. -/
theorem ofNatCounts_jeffreysPosterior_eq_predJeffreys
    (nPos nNeg : ℕ) :
    posteriorMeanStrength
        Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys
        (ofNatCounts nPos nNeg) =
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predJeffreys nPos nNeg := by
  have hhalf : ((0.5 : ℝ≥0∞).toReal : ℝ) = (1 / 2 : ℝ) := by
    have eq1 : (0.5 : ℝ≥0∞) = (↑(0.5 : ℝ≥0) : ℝ≥0∞) := rfl
    rw [eq1, ENNReal.coe_toReal]
    norm_num
  simp [posteriorMeanStrength, posteriorDenom, ofNatCounts, total,
    Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys,
    Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predJeffreys,
    Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.jeffreysPosteriorMean,
    Mettapedia.PLN.Evidence.EvidenceCounts.jeffreysPosteriorMean, hhalf]
  ring_nf

/-- Nat-count prior canary, transported to the real-valued truth tower:
with one negative observation, Haldane/PLN strength, Jeffreys/KT, and
Laplace/uniform display different strengths. -/
theorem ofNatCounts_prior_matters_example :
    (ofNatCounts 0 1).mleStrength = 0 ∧
      posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys
          (ofNatCounts 0 1) =
        (1 / 4 : ℝ) ∧
        posteriorMeanStrength
            Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
            (ofNatCounts 0 1) =
          (1 / 3 : ℝ) := by
  have h := Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.prior_matters_example
  rw [ofNatCounts_mleStrength_eq_predHaldane,
    ofNatCounts_jeffreysPosterior_eq_predJeffreys,
    ofNatCounts_uniformPosterior_eq_predLaplace]
  exact h

/-- Laplace/uniform posterior strength differs from Haldane/PLN strength by
the existing `O(1/n)` Nat-count bound, now phrased over `BinaryCounts`. -/
theorem ofNatCounts_haldane_vs_laplace_difference
    (nPos nNeg : ℕ) (h : nPos + nNeg ≠ 0) :
    |(ofNatCounts nPos nNeg).mleStrength -
        posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
          (ofNatCounts nPos nNeg)| ≤
      2 / ((nPos : ℝ) + (nNeg : ℝ) + 2) := by
  rw [ofNatCounts_mleStrength_eq_predHaldane,
    ofNatCounts_uniformPosterior_eq_predLaplace]
  exact Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.haldane_vs_laplace_difference nPos nNeg h

/-- Jeffreys/KT posterior strength differs from Haldane/PLN strength by the
existing `O(1/n)` Nat-count bound, now phrased over `BinaryCounts`. -/
theorem ofNatCounts_haldane_vs_jeffreys_difference
    (nPos nNeg : ℕ) (h : nPos + nNeg ≠ 0) :
    |(ofNatCounts nPos nNeg).mleStrength -
        posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys
          (ofNatCounts nPos nNeg)| ≤
      1 / (2 * ((nPos : ℝ) + (nNeg : ℝ) + 1)) := by
  rw [ofNatCounts_mleStrength_eq_predHaldane,
    ofNatCounts_jeffreysPosterior_eq_predJeffreys]
  exact Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.haldane_vs_jeffreys_difference nPos nNeg h

/-- Existing convergence theorem, re-exposed at the truth-tower boundary:
Haldane/PLN strength converges to the proper symmetric-prior posterior mean as
sample size grows. -/
theorem ofNatCounts_mle_converges_to_symmetric_posterior_mean :
    ∀ ε : ℝ, 0 < ε → ∀ priorParam : ℝ, 0 < priorParam →
      ∃ N : ℕ, ∀ nPos nNeg : ℕ, nPos + nNeg ≥ N → nPos + nNeg ≠ 0 →
        let strength := (ofNatCounts nPos nNeg).mleStrength
        let mean :=
          ((nPos : ℝ) + priorParam) /
            ((nPos : ℝ) + (nNeg : ℝ) + 2 * priorParam)
        |strength - mean| < ε := by
  intro ε hε priorParam hprior
  obtain ⟨N, hN⟩ :=
    Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.strength_converges_to_mean
      ε hε priorParam hprior
  refine ⟨N, ?_⟩
  intro nPos nNeg hn hne
  have h := hN nPos nNeg hn hne
  rw [ofNatCounts_mleStrength_eq_predHaldane]
  simpa [Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predHaldane] using h

/-- A strength plus an arbitrary evidence-weight coordinate for total evidence. -/
noncomputable def toSTV (χ : EvidenceWeightCoordinate) (e : BinaryCounts) : ℝ × ℝ :=
  χ.encodeCounts e.nPlus e.nMinus

/-- Any valid evidence-weight coordinate reconstructs the finite binary counts.

This is the minimal mathematical requirement for a confidence-like coordinate:
not the PLN formula, but recoverability of the total evidence weight. -/
theorem toSTV_decodes_counts
    (χ : EvidenceWeightCoordinate) (e : BinaryCounts)
    (hTotal : e.total ≠ 0) :
    χ.decodeCounts (e.toSTV χ) = (e.nPlus, e.nMinus) := by
  simpa [toSTV, total] using
    χ.decode_encode_counts e.nPlus_nonneg e.nMinus_nonneg hTotal

/-- Two coordinates may display different confidence values while carrying the
same finite evidence counts.  The counts are the state; the coordinate is a
view. -/
theorem reserveHalf_and_pln_both_decode_counts
    (k : ℝ) (hk : 0 < k) (e : BinaryCounts) (hTotal : e.total ≠ 0) :
    (plnOddsCoordinate k hk).decodeCounts (e.toSTV (plnOddsCoordinate k hk)) =
        (e.nPlus, e.nMinus) ∧
      (reserveHalfCoordinate k hk).decodeCounts
          (e.toSTV (reserveHalfCoordinate k hk)) =
        (e.nPlus, e.nMinus) := by
  constructor
  · exact e.toSTV_decodes_counts (plnOddsCoordinate k hk) hTotal
  · exact e.toSTV_decodes_counts (reserveHalfCoordinate k hk) hTotal

/-- Add finite binary evidence counts componentwise. -/
def add (e₁ e₂ : BinaryCounts) : BinaryCounts where
  nPlus := e₁.nPlus + e₂.nPlus
  nMinus := e₁.nMinus + e₂.nMinus
  nPlus_nonneg := add_nonneg e₁.nPlus_nonneg e₂.nPlus_nonneg
  nMinus_nonneg := add_nonneg e₁.nMinus_nonneg e₂.nMinus_nonneg

@[simp] theorem add_total (e₁ e₂ : BinaryCounts) :
    (e₁.add e₂).total = e₁.total + e₂.total := by
  simp [add, total]
  ring

theorem strength_mul_total (e : BinaryCounts) (nonzero : e.total ≠ 0) :
    e.strength * e.total = e.nPlus :=
  div_mul_cancel₀ _ nonzero

/-- Strength of added positive-total counts is the total-evidence weighted
mixture of the input strengths. -/
theorem add_strength_eq_weighted_mixture
    (e₁ e₂ : BinaryCounts)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (_hSum : e₁.total + e₂.total ≠ 0) :
    (e₁.add e₂).strength =
      (e₁.strength * e₁.total + e₂.strength * e₂.total) /
        (e₁.total + e₂.total) := by
  rw [e₁.strength_mul_total h₁, e₂.strength_mul_total h₂, strength, add_total]
  rfl

end BinaryCounts

end Mettapedia.PLN.TruthValues.PLNTruthTower
