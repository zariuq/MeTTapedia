import Mettapedia.Logic.PLNIndefiniteTruth
import Mettapedia.Logic.PLNForcedQueries
import Mettapedia.Logic.EvidenceBeta
import Mettapedia.Logic.WalleyBinaryIDM
import Mettapedia.Logic.WalleyMultinomialIDM
import Mettapedia.ProbabilityTheory.ImpreciseProbability.Basic
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
import Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics
import KnuthSkilling.Core.TotalityImprecision

/-!
# PLN Truth Tower

This module assembles the currently separate PLN truth-value layers into a
small integration surface:

* finite binary evidence counts are the load-bearing state;
* strength plus a confidence-like coordinate is a reversible view only when
  the coordinate has a left inverse on nonnegative total evidence;
* generic indefinite truth values keep interval width and credibility
  independent;
* Walley's binary IDM predictive slice is an extra bridge law that forces the
  usual PLN/NARS odds confidence coordinate.

The file is intentionally modest: it packages existing theorems and adds the
interface lemmas needed to make the degrees of freedom visible at the type
level.
-/

namespace Mettapedia.Logic.PLNTruthTower

open scoped ENNReal NNReal Pointwise

open Mettapedia.Logic.PLNConfidenceWeight
open Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.Logic.PLNIndefiniteTruth
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

universe u v w

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
  by_contra hNotPos
  have hLe : e.total ≤ 0 := le_of_not_gt hNotPos
  have hZero : e.total = 0 := le_antisymm hLe e.total_nonneg
  exact hTotal hZero

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
  unfold total at hPos ⊢
  linarith [e.nMinus_nonneg]

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
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
    (e : BinaryCounts) : ℝ :=
  ctx.α₀.toReal + ctx.β₀.toReal + e.total

/-- Contextual Beta-posterior mean strength projection.  Unlike PLN simple
strength, this projection makes the prior/context degree of freedom explicit. -/
noncomputable def posteriorMeanStrength
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
    (e : BinaryCounts) : ℝ :=
  (ctx.α₀.toReal + e.nPlus) / posteriorDenom ctx e

/-- The posterior denominator is always nonnegative. -/
theorem posteriorDenom_nonneg
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
    (e : BinaryCounts) :
    0 ≤ posteriorDenom ctx e := by
  unfold posteriorDenom
  have hα : 0 ≤ ctx.α₀.toReal := ENNReal.toReal_nonneg
  have hβ : 0 ≤ ctx.β₀.toReal := ENNReal.toReal_nonneg
  have ht : 0 ≤ e.total := e.total_nonneg
  linarith

/-- The contextual posterior-mean strength is a unit interval value whenever
its denominator is genuinely positive. -/
theorem posteriorMeanStrength_in_unit_of_pos_denom
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
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
    posteriorMeanStrength Mettapedia.Logic.EvidenceClass.BinaryContext.improper e =
      e.mleStrength := by
  simp [posteriorMeanStrength, posteriorDenom, mleStrength, strength,
    total, Mettapedia.Logic.EvidenceClass.BinaryContext.improper]

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
          Mettapedia.Logic.EvidenceClass.BinaryContext.uniform singlePositive =
        (2 / 3 : ℝ) ∧
        singlePositive.mleStrength ≠
          posteriorMeanStrength
            Mettapedia.Logic.EvidenceClass.BinaryContext.uniform singlePositive := by
  norm_num [singlePositive, mleStrength, strength, posteriorMeanStrength,
    posteriorDenom, total, Mettapedia.Logic.EvidenceClass.BinaryContext.uniform]

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
      Mettapedia.Logic.EvidenceBeta.predHaldane nPos nNeg := by
  by_cases h : nPos + nNeg = 0
  · have hPos : nPos = 0 := Nat.eq_zero_of_add_eq_zero_right h
    have hNeg : nNeg = 0 := Nat.eq_zero_of_add_eq_zero_left h
    simp [ofNatCounts, mleStrength, strength, total,
      Mettapedia.Logic.EvidenceBeta.predHaldane,
      Mettapedia.Logic.EvidenceBeta.plnStrength,
      Mettapedia.Logic.EvidenceCounts.plnStrength, hPos, hNeg]
  · have hTower :
        (ofNatCounts nPos nNeg).mleStrength =
          (nPos : ℝ) / ((nPos + nNeg : ℕ) : ℝ) := by
      simp [ofNatCounts, mleStrength, strength, total, Nat.cast_add]
    have hLedger :
        Mettapedia.Logic.EvidenceBeta.predHaldane nPos nNeg =
          (nPos : ℝ) / ((nPos + nNeg : ℕ) : ℝ) := by
      simpa [Mettapedia.Logic.EvidenceBeta.predHaldane] using
        Mettapedia.Logic.EvidenceBeta.plnStrength_eq_improper_mean nPos nNeg h
    rw [hTower, hLedger]

/-- The real-valued uniform-prior projection agrees with the existing
Nat-count Laplace/uniform posterior-mean ledger. -/
theorem ofNatCounts_uniformPosterior_eq_predLaplace
    (nPos nNeg : ℕ) :
    posteriorMeanStrength
        Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
        (ofNatCounts nPos nNeg) =
      Mettapedia.Logic.EvidenceBeta.predLaplace nPos nNeg := by
  simp [posteriorMeanStrength, posteriorDenom, ofNatCounts, total,
    Mettapedia.Logic.EvidenceClass.BinaryContext.uniform,
    Mettapedia.Logic.EvidenceBeta.predLaplace,
    Mettapedia.Logic.EvidenceBeta.uniformPosteriorMean,
    Mettapedia.Logic.EvidenceCounts.uniformPosteriorMean]
  ring_nf

/-- The real-valued Jeffreys-prior projection agrees with the existing
Nat-count Jeffreys/KT posterior-mean ledger. -/
theorem ofNatCounts_jeffreysPosterior_eq_predJeffreys
    (nPos nNeg : ℕ) :
    posteriorMeanStrength
        Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
        (ofNatCounts nPos nNeg) =
      Mettapedia.Logic.EvidenceBeta.predJeffreys nPos nNeg := by
  have hhalf : ((0.5 : ℝ≥0∞).toReal : ℝ) = (1 / 2 : ℝ) := by
    have eq1 : (0.5 : ℝ≥0∞) = (↑(0.5 : ℝ≥0) : ℝ≥0∞) := rfl
    rw [eq1, ENNReal.coe_toReal]
    norm_num
  simp [posteriorMeanStrength, posteriorDenom, ofNatCounts, total,
    Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys,
    Mettapedia.Logic.EvidenceBeta.predJeffreys,
    Mettapedia.Logic.EvidenceBeta.jeffreysPosteriorMean,
    Mettapedia.Logic.EvidenceCounts.jeffreysPosteriorMean, hhalf]
  ring_nf

/-- Nat-count prior canary, transported to the real-valued truth tower:
with one negative observation, Haldane/PLN strength, Jeffreys/KT, and
Laplace/uniform display different strengths. -/
theorem ofNatCounts_prior_matters_example :
    (ofNatCounts 0 1).mleStrength = 0 ∧
      posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
          (ofNatCounts 0 1) =
        (1 / 4 : ℝ) ∧
        posteriorMeanStrength
            Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
            (ofNatCounts 0 1) =
          (1 / 3 : ℝ) := by
  have h := Mettapedia.Logic.EvidenceBeta.prior_matters_example
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
          Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
          (ofNatCounts nPos nNeg)| ≤
      2 / ((nPos : ℝ) + (nNeg : ℝ) + 2) := by
  rw [ofNatCounts_mleStrength_eq_predHaldane,
    ofNatCounts_uniformPosterior_eq_predLaplace]
  exact Mettapedia.Logic.EvidenceBeta.haldane_vs_laplace_difference nPos nNeg h

/-- Jeffreys/KT posterior strength differs from Haldane/PLN strength by the
existing `O(1/n)` Nat-count bound, now phrased over `BinaryCounts`. -/
theorem ofNatCounts_haldane_vs_jeffreys_difference
    (nPos nNeg : ℕ) (h : nPos + nNeg ≠ 0) :
    |(ofNatCounts nPos nNeg).mleStrength -
        posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
          (ofNatCounts nPos nNeg)| ≤
      1 / (2 * ((nPos : ℝ) + (nNeg : ℝ) + 1)) := by
  rw [ofNatCounts_mleStrength_eq_predHaldane,
    ofNatCounts_jeffreysPosterior_eq_predJeffreys]
  exact Mettapedia.Logic.EvidenceBeta.haldane_vs_jeffreys_difference nPos nNeg h

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
    Mettapedia.Logic.EvidenceBeta.strength_converges_to_mean
      ε hε priorParam hprior
  refine ⟨N, ?_⟩
  intro nPos nNeg hn hne
  have h := hN nPos nNeg hn hne
  rw [ofNatCounts_mleStrength_eq_predHaldane]
  simpa [Mettapedia.Logic.EvidenceBeta.predHaldane] using h

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

/-- Strength of added positive-total counts is the total-evidence weighted
mixture of the input strengths. -/
theorem add_strength_eq_weighted_mixture
    (e₁ e₂ : BinaryCounts)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (_hSum : e₁.total + e₂.total ≠ 0) :
    (e₁.add e₂).strength =
      (e₁.strength * e₁.total + e₂.strength * e₂.total) /
        (e₁.total + e₂.total) := by
  have h₁mul : e₁.strength * e₁.total = e₁.nPlus := by
    unfold strength
    field_simp [h₁]
  have h₂mul : e₂.strength * e₂.total = e₂.nPlus := by
    unfold strength
    field_simp [h₂]
  calc
    (e₁.add e₂).strength =
        (e₁.nPlus + e₂.nPlus) / (e₁.total + e₂.total) := by
      unfold strength
      rw [add_total]
      rfl
    _ = (e₁.strength * e₁.total + e₂.strength * e₂.total) /
        (e₁.total + e₂.total) := by
      rw [h₁mul, h₂mul]

end BinaryCounts

/-! ## Typed STV views -/

/-- A simple truth-value view whose confidence coordinate carries its
evidence-weight coordinate as type-level provenance. -/
structure TypedSTV (χ : EvidenceWeightCoordinate) where
  strength : ℝ
  confidence : TypedConfidence χ

namespace TypedSTV

/-- Decode the confidence coordinate back to total evidence weight. -/
noncomputable def weight {χ : EvidenceWeightCoordinate} (tv : TypedSTV χ) : ℝ :=
  tv.confidence.weight

/-- Decode a typed STV view back to positive/negative finite evidence counts. -/
noncomputable def decodeCounts {χ : EvidenceWeightCoordinate} (tv : TypedSTV χ) : ℝ × ℝ :=
  (tv.strength * tv.weight, (1 - tv.strength) * tv.weight)

/-- Project finite binary evidence counts to a typed STV view. -/
noncomputable def fromCounts (χ : EvidenceWeightCoordinate) (e : BinaryCounts) :
    TypedSTV χ where
  strength := e.strength
  confidence := TypedConfidence.ofWeight χ e.total

@[simp] theorem weight_fromCounts (χ : EvidenceWeightCoordinate) (e : BinaryCounts) :
    (fromCounts χ e).weight = e.total := by
  unfold fromCounts weight
  exact TypedConfidence.weight_ofWeight χ e.total_nonneg

/-- Typed STV projection is a reversible view of positive-total evidence
counts for any valid confidence coordinate. -/
theorem decode_fromCounts
    (χ : EvidenceWeightCoordinate) (e : BinaryCounts)
    (hTotal : e.total ≠ 0) :
    (fromCounts χ e).decodeCounts = (e.nPlus, e.nMinus) := by
  have hTotal' : e.nPlus + e.nMinus ≠ 0 := by
    simpa [BinaryCounts.total] using hTotal
  unfold decodeCounts
  rw [weight_fromCounts]
  simp [fromCounts, BinaryCounts.strength]
  constructor
  · field_simp [hTotal']
  · field_simp [hTotal']
    ring

/-- Orthogonality canary: even under one fixed confidence coordinate, equal
strength does not determine the displayed confidence.  The two examples have
the same positive/negative ratio but different total evidence. -/
theorem same_strength_can_have_different_confidence :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := fromCounts χ (BinaryCounts.ofNatCounts 1 1)
    let y := fromCounts χ (BinaryCounts.ofNatCounts 2 2)
    x.strength = y.strength ∧ x.confidence.display ≠ y.confidence.display := by
  norm_num [fromCounts, TypedConfidence.ofWeight, BinaryCounts.ofNatCounts,
    BinaryCounts.strength, BinaryCounts.total, plnOddsCoordinate]

/-- Orthogonality canary: even under one fixed confidence coordinate, equal
displayed confidence does not determine strength.  The two examples have the
same total evidence but different positive/negative split. -/
theorem same_confidence_can_have_different_strength :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := fromCounts χ (BinaryCounts.ofNatCounts 1 1)
    let y := fromCounts χ (BinaryCounts.ofNatCounts 2 0)
    x.confidence.display = y.confidence.display ∧ x.strength ≠ y.strength := by
  norm_num [fromCounts, TypedConfidence.ofWeight, BinaryCounts.ofNatCounts,
    BinaryCounts.strength, BinaryCounts.total, plnOddsCoordinate]

/-- Same-coordinate revision: weighted-average strength plus additive evidence
weight.  The shared coordinate index prevents silent cross-coordinate revision. -/
noncomputable def revise {χ : EvidenceWeightCoordinate}
    (x y : TypedSTV χ) : TypedSTV χ where
  strength := (x.strength * x.weight + y.strength * y.weight) /
    (x.weight + y.weight)
  confidence := TypedConfidence.addByWeight x.confidence y.confidence

@[simp] theorem weight_revise {χ : EvidenceWeightCoordinate}
    (x y : TypedSTV χ) (hx : 0 ≤ x.weight) (hy : 0 ≤ y.weight) :
    (revise x y).weight = x.weight + y.weight := by
  unfold revise weight
  exact TypedConfidence.weight_addByWeight x.confidence y.confidence hx hy

@[simp] theorem strength_revise {χ : EvidenceWeightCoordinate}
    (x y : TypedSTV χ) :
    (revise x y).strength =
      (x.strength * x.weight + y.strength * y.weight) /
        (x.weight + y.weight) :=
  rfl

/-- Revision at the typed-STV layer is exactly addition at the decoded evidence
count layer. -/
theorem decode_revise {χ : EvidenceWeightCoordinate} (x y : TypedSTV χ)
    (hx : 0 ≤ x.weight) (hy : 0 ≤ y.weight)
    (hsum : x.weight + y.weight ≠ 0) :
    (revise x y).decodeCounts =
      (x.decodeCounts.1 + y.decodeCounts.1, x.decodeCounts.2 + y.decodeCounts.2) := by
  unfold decodeCounts
  rw [weight_revise x y hx hy]
  unfold revise
  simp
  constructor
  · field_simp [hsum]
  · field_simp [hsum]
    ring

end TypedSTV

/-- Revision of typed STV views built from evidence counts decodes to
componentwise evidence addition. -/
theorem typedSTV_revision_fromCounts_decodes_added_counts
    (χ : EvidenceWeightCoordinate) (e₁ e₂ : BinaryCounts)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (hSum : e₁.total + e₂.total ≠ 0) :
    (TypedSTV.revise (TypedSTV.fromCounts χ e₁)
      (TypedSTV.fromCounts χ e₂)).decodeCounts =
        ((e₁.add e₂).nPlus, (e₁.add e₂).nMinus) := by
  rw [TypedSTV.decode_revise]
  · rw [TypedSTV.decode_fromCounts χ e₁ h₁,
      TypedSTV.decode_fromCounts χ e₂ h₂]
    rfl
  · rw [TypedSTV.weight_fromCounts]
    exact e₁.total_nonneg
  · rw [TypedSTV.weight_fromCounts]
    exact e₂.total_nonneg
  · rw [TypedSTV.weight_fromCounts, TypedSTV.weight_fromCounts]
    exact hSum

/-- Revision of typed STV views built from raw counts uses the weighted
mixture of the input strengths.  This is the mixture-coordinate view of the
same raw-count addition theorem above. -/
theorem typedSTV_revision_fromCounts_strength_eq_weighted_mixture
    (χ : EvidenceWeightCoordinate) (e₁ e₂ : BinaryCounts) :
    (TypedSTV.revise (TypedSTV.fromCounts χ e₁)
      (TypedSTV.fromCounts χ e₂)).strength =
        (e₁.strength * e₁.total + e₂.strength * e₂.total) /
          (e₁.total + e₂.total) := by
  rw [TypedSTV.strength_revise]
  rw [TypedSTV.weight_fromCounts, TypedSTV.weight_fromCounts]
  simp [TypedSTV.fromCounts]

/-! ## Typed categorical truth views -/

/-- A categorical truth-value view whose mean vector is paired with a typed
confidence coordinate for total evidence.  This is the multinomial analogue of
`TypedSTV`: the mean vector is the direction, and the typed confidence carries
the total concentration with coordinate provenance. -/
structure TypedCategoricalTruth
    (k : ℕ) (χ : EvidenceWeightCoordinate) where
  mean : Fin k → ℝ
  confidence : TypedConfidence χ

namespace TypedCategoricalTruth

/-- Decode the confidence coordinate back to total evidence weight. -/
noncomputable def weight {k : ℕ} {χ : EvidenceWeightCoordinate}
    (tv : TypedCategoricalTruth k χ) : ℝ :=
  tv.confidence.weight

/-- Decode a categorical truth view back to real-valued category counts. -/
noncomputable def decodeCounts {k : ℕ} {χ : EvidenceWeightCoordinate}
    (tv : TypedCategoricalTruth k χ) : Fin k → ℝ :=
  fun i => tv.mean i * tv.weight

/-- Project finite categorical evidence counts to a typed categorical view. -/
noncomputable def fromCounts {k : ℕ} (χ : EvidenceWeightCoordinate)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) :
    TypedCategoricalTruth k χ where
  mean := fun i => (e.counts i : ℝ) / (e.total : ℝ)
  confidence := TypedConfidence.ofWeight χ (e.total : ℝ)

@[simp] theorem weight_fromCounts {k : ℕ}
    (χ : EvidenceWeightCoordinate)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) :
    (fromCounts χ e).weight = (e.total : ℝ) := by
  unfold fromCounts weight
  exact TypedConfidence.weight_ofWeight χ (by exact_mod_cast (Nat.zero_le e.total))

/-- Typed categorical projection is a reversible view of positive-total
categorical evidence counts, pointwise in every category. -/
theorem decode_fromCounts {k : ℕ}
    (χ : EvidenceWeightCoordinate)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (hTotal : e.total ≠ 0) (i : Fin k) :
    (fromCounts χ e).decodeCounts i = (e.counts i : ℝ) := by
  have hTotalR : (e.total : ℝ) ≠ 0 := by
    exact_mod_cast hTotal
  unfold decodeCounts
  rw [weight_fromCounts]
  simp [fromCounts]
  field_simp [hTotalR]

/-- Same-coordinate categorical revision: weighted-average mean vector plus
additive evidence weight. -/
noncomputable def revise {k : ℕ} {χ : EvidenceWeightCoordinate}
    (x y : TypedCategoricalTruth k χ) : TypedCategoricalTruth k χ where
  mean := fun i => (x.mean i * x.weight + y.mean i * y.weight) /
    (x.weight + y.weight)
  confidence := TypedConfidence.addByWeight x.confidence y.confidence

@[simp] theorem weight_revise {k : ℕ} {χ : EvidenceWeightCoordinate}
    (x y : TypedCategoricalTruth k χ) (hx : 0 ≤ x.weight) (hy : 0 ≤ y.weight) :
    (revise x y).weight = x.weight + y.weight := by
  unfold revise weight
  exact TypedConfidence.weight_addByWeight x.confidence y.confidence hx hy

/-- Revision at the typed categorical layer is exactly addition at the decoded
category-count layer. -/
theorem decode_revise {k : ℕ} {χ : EvidenceWeightCoordinate}
    (x y : TypedCategoricalTruth k χ)
    (hx : 0 ≤ x.weight) (hy : 0 ≤ y.weight)
    (hsum : x.weight + y.weight ≠ 0) (i : Fin k) :
    (revise x y).decodeCounts i =
      x.decodeCounts i + y.decodeCounts i := by
  unfold decodeCounts
  rw [weight_revise x y hx hy]
  unfold revise
  field_simp [hsum]

end TypedCategoricalTruth

/-- Revision of typed categorical views built from evidence counts decodes to
componentwise categorical evidence addition. -/
theorem typedCategorical_revision_fromCounts_decodes_added_counts
    {k : ℕ} (χ : EvidenceWeightCoordinate)
    (e₁ e₂ : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (hSum : (e₁.total : ℝ) + (e₂.total : ℝ) ≠ 0) (i : Fin k) :
    (TypedCategoricalTruth.revise
      (TypedCategoricalTruth.fromCounts χ e₁)
      (TypedCategoricalTruth.fromCounts χ e₂)).decodeCounts i =
        ((e₁ + e₂).counts i : ℝ) := by
  rw [TypedCategoricalTruth.decode_revise]
  · rw [TypedCategoricalTruth.decode_fromCounts χ e₁ h₁ i,
      TypedCategoricalTruth.decode_fromCounts χ e₂ h₂ i]
    change (e₁.counts i : ℝ) + (e₂.counts i : ℝ) =
      ((e₁.counts i + e₂.counts i : ℕ) : ℝ)
    exact (Nat.cast_add (e₁.counts i) (e₂.counts i)).symm
  · rw [TypedCategoricalTruth.weight_fromCounts]
    exact_mod_cast (Nat.zero_le e₁.total)
  · rw [TypedCategoricalTruth.weight_fromCounts]
    exact_mod_cast (Nat.zero_le e₂.total)
  · rw [TypedCategoricalTruth.weight_fromCounts,
      TypedCategoricalTruth.weight_fromCounts]
    exact hSum

/-! ## Typed confidence compatibility guard -/

/-- Same-coordinate typed confidence values can be combined by minimum in
evidence-weight space and recover the exact minimum weight.  This is the typed
form of the conjunction-confidence boundary: the coordinate is provenance, not
just a displayed number. -/
theorem typedConfidence_min_same_coordinate_recovers_min_weight
    (χ : EvidenceWeightCoordinate) {w₁ w₂ : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    let c₁ := TypedConfidence.ofWeight χ w₁
    let c₂ := TypedConfidence.ofWeight χ w₂
    (TypedConfidence.minByWeight c₁ c₂).weight = min w₁ w₂ := by
  dsimp
  have hc₁ : 0 ≤ (TypedConfidence.ofWeight χ w₁).weight := by
    rw [TypedConfidence.weight_ofWeight χ hw₁]
    exact hw₁
  have hc₂ : 0 ≤ (TypedConfidence.ofWeight χ w₂).weight := by
    rw [TypedConfidence.weight_ofWeight χ hw₂]
    exact hw₂
  calc
    (TypedConfidence.minByWeight (TypedConfidence.ofWeight χ w₁)
        (TypedConfidence.ofWeight χ w₂)).weight =
        min (TypedConfidence.ofWeight χ w₁).weight
          (TypedConfidence.ofWeight χ w₂).weight :=
          TypedConfidence.weight_minByWeight _ _ hc₁ hc₂
    _ = min w₁ w₂ := by
          rw [TypedConfidence.weight_ofWeight χ hw₁,
            TypedConfidence.weight_ofWeight χ hw₂]

/-- Same-coordinate typed confidence values can also model revision-style
evidence accumulation by adding decoded weights and re-encoding in the same
coordinate. -/
theorem typedConfidence_add_same_coordinate_recovers_sum_weight
    (χ : EvidenceWeightCoordinate) {w₁ w₂ : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    let c₁ := TypedConfidence.ofWeight χ w₁
    let c₂ := TypedConfidence.ofWeight χ w₂
    (TypedConfidence.addByWeight c₁ c₂).weight = w₁ + w₂ := by
  dsimp
  have hc₁ : 0 ≤ (TypedConfidence.ofWeight χ w₁).weight := by
    rw [TypedConfidence.weight_ofWeight χ hw₁]
    exact hw₁
  have hc₂ : 0 ≤ (TypedConfidence.ofWeight χ w₂).weight := by
    rw [TypedConfidence.weight_ofWeight χ hw₂]
    exact hw₂
  calc
    (TypedConfidence.addByWeight (TypedConfidence.ofWeight χ w₁)
        (TypedConfidence.ofWeight χ w₂)).weight =
        (TypedConfidence.ofWeight χ w₁).weight +
          (TypedConfidence.ofWeight χ w₂).weight :=
          TypedConfidence.weight_addByWeight _ _ hc₁ hc₂
    _ = w₁ + w₂ := by
          rw [TypedConfidence.weight_ofWeight χ hw₁,
            TypedConfidence.weight_ofWeight χ hw₂]

/-- Canary: raw display equality is not a safe compatibility test.  The same
display value can decode to different weights when the coordinate provenance
differs. -/
theorem raw_display_equality_does_not_determine_weight :
    let χp := plnOddsCoordinate 1 (by norm_num)
    let χr := reserveHalfCoordinate 1 (by norm_num)
    let cp : TypedConfidence χp := ⟨(1 / 3 : ℝ)⟩
    let cr : TypedConfidence χr := ⟨(1 / 3 : ℝ)⟩
    cp.display = cr.display ∧ cp.weight ≠ cr.weight :=
  TypedConfidence.same_display_can_decode_differently

/-! ## Generic ITV freedom -/

/-- Generic ITVs do not determine credibility from width alone. -/
theorem genericITV_width_does_not_determine_credibility :
    ∃ itv₀ itv₁ : ITV,
      itv₀.width = itv₁.width ∧ itv₀.credibility ≠ itv₁.credibility :=
  ITV.generic_width_does_not_determine_credibility

/-- Generic ITVs do not determine width from credibility alone. -/
theorem genericITV_credibility_does_not_determine_width :
    ∃ itv₀ itv₁ : ITV,
      itv₀.credibility = itv₁.credibility ∧ itv₀.width ≠ itv₁.width :=
  ITV.generic_credibility_does_not_determine_width

/-! ## Typed ITV constructor provenance -/

/-- A constructor semantics for indefinite truth values.  The `Source` is the
load-bearing input data for this semantics; the raw `ITV` is its projection. -/
structure ITVSemantics where
  Source : Type u
  toITV : Source → ITV

/-- An ITV tagged by the constructor semantics that produced it.  Consumers can
require the same semantics parameter to avoid silently mixing generic, Bayesian,
and Walley-style interval interpretations. -/
structure TypedITV (Sem : ITVSemantics.{u}) where
  source : Sem.Source

namespace TypedITV

/-- Forget constructor provenance and recover the raw ITV view. -/
noncomputable def value {Sem : ITVSemantics} (x : TypedITV Sem) : ITV :=
  Sem.toITV x.source

noncomputable def lower {Sem : ITVSemantics} (x : TypedITV Sem) : ℝ :=
  x.value.lower

noncomputable def upper {Sem : ITVSemantics} (x : TypedITV Sem) : ℝ :=
  x.value.upper

noncomputable def width {Sem : ITVSemantics} (x : TypedITV Sem) : ℝ :=
  x.value.width

noncomputable def credibility {Sem : ITVSemantics} (x : TypedITV Sem) : ℝ :=
  x.value.credibility

/-- The current midpoint point-estimate view of a typed ITV.  This is a
projection of the interval, not extra constructor provenance. -/
noncomputable def midpoint {Sem : ITVSemantics} (x : TypedITV Sem) : ℝ :=
  x.value.strength

@[simp] theorem midpoint_eq_strength {Sem : ITVSemantics} (x : TypedITV Sem) :
    x.midpoint = x.value.strength :=
  rfl

/-- The lower endpoint is below the midpoint point-estimate view. -/
theorem lower_le_midpoint {Sem : ITVSemantics} (x : TypedITV Sem) :
    x.lower ≤ x.midpoint := by
  let y := x.value
  change y.lower ≤ (y.lower + y.upper) / 2
  calc
    y.lower = (2 * y.lower) / 2 := by ring
    _ ≤ (y.lower + y.upper) / 2 := by
      apply div_le_div_of_nonneg_right
      · linarith [y.lower_le_upper]
      · norm_num

/-- The midpoint point-estimate view is below the upper endpoint. -/
theorem midpoint_le_upper {Sem : ITVSemantics} (x : TypedITV Sem) :
    x.midpoint ≤ x.upper := by
  let y := x.value
  change (y.lower + y.upper) / 2 ≤ y.upper
  calc
    (y.lower + y.upper) / 2 ≤ (2 * y.upper) / 2 := by
      apply div_le_div_of_nonneg_right
      · linarith [y.lower_le_upper]
      · norm_num
    _ = y.upper := by ring

/-- The midpoint point-estimate view lies in the unit interval. -/
theorem midpoint_in_unit {Sem : ITVSemantics} (x : TypedITV Sem) :
    x.midpoint ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [midpoint] using x.value.strength_in_unit

/-- A same-semantics comparison.  The shared `Sem` parameter is the compatibility
guard; differently constructed ITVs need an explicit bridge before using this
operation. -/
def credibilityLE {Sem : ITVSemantics} (x y : TypedITV Sem) : Prop :=
  x.credibility ≤ y.credibility

end TypedITV

/-- A raw unary ITV operation, separated from its typed/provenance wrapper. -/
structure ITVUnaryOperation where
  eval : ITV → ITV

/-- A raw binary ITV operation, separated from its typed/provenance wrapper. -/
structure ITVBinaryOperation where
  eval : ITV → ITV → ITV

/-- Raw negation as an operation descriptor. -/
def negationOperation : ITVUnaryOperation where
  eval := ITV.negation

/-- Raw conjunction as an operation descriptor. -/
noncomputable def conjunctionOperation : ITVBinaryOperation where
  eval := ITV.conjunction

/-- Raw disjunction as an operation descriptor. -/
noncomputable def disjunctionOperation : ITVBinaryOperation where
  eval := ITV.disjunction

/-- Raw implication as an operation descriptor. -/
noncomputable def implicationOperation : ITVBinaryOperation where
  eval := ITV.implication

/-- Provenance for a typed ITV obtained by applying a unary operation to a
typed ITV.  The result is not claimed to have the same constructor semantics;
its source explicitly records the operation and input. -/
noncomputable def derivedUnaryITVSemantics
    (Sem : ITVSemantics) (op : ITVUnaryOperation) : ITVSemantics where
  Source := TypedITV Sem
  toITV := fun x => op.eval x.value

/-- Provenance for a typed ITV obtained by applying a binary operation to two
typed ITVs with the same semantics.  The shared `Sem` parameter is the
compatibility guard; the output is a derived-operation semantics, not a silent
reuse of `Sem`. -/
noncomputable def derivedBinaryITVSemantics
    (Sem : ITVSemantics) (op : ITVBinaryOperation) : ITVSemantics where
  Source := TypedITV Sem × TypedITV Sem
  toITV := fun xy => op.eval xy.1.value xy.2.value

/-- The fully generic ITV semantics carries a raw ITV as its source. -/
def genericITVSemantics : ITVSemantics where
  Source := ITV
  toITV := id

/-- Source data for Bayesian credible-interval ITV semantics at fixed level. -/
structure BayesCredibleITVSource (level : ℝ) where
  evidence : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence
  level_ok : 0 < level ∧ level < 1

/-- Source data for Walley binary-IDM ITV semantics at fixed IDM strength. -/
structure WalleyBinaryITVSource (s : ℝ) where
  evidence : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence
  s_pos : 0 < s

/-- Source data for Walley categorical-IDM ITV semantics at fixed IDM context.
The queried category is part of the source, because each category has its own
lower/upper envelope. -/
structure WalleyCategoricalITVSource (k : ℕ) where
  evidence : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k
  category : Fin k

/-- The categorical Walley-IDM interval for one queried category, projected to
the generic `ITV` record.  The interval endpoints are Walley's IDM lower/upper
predictive probabilities; credibility is the complementary precision proxy
`n/(n+s)`. -/
noncomputable def walleyCategoricalITV {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    ITV where
  lower := Mettapedia.Logic.EvidenceDirichlet.idmLower ctx e i
  upper := Mettapedia.Logic.EvidenceDirichlet.idmUpper ctx e i
  credibility := (e.total : ℝ) /
    Mettapedia.Logic.EvidenceDirichlet.idmDenom ctx e
  lower_le_upper :=
    Mettapedia.Logic.EvidenceDirichlet.idmLower_le_idmUpper ctx e i
  lower_in_unit := by
    exact ⟨
      Mettapedia.Logic.EvidenceDirichlet.idmLower_nonneg ctx e i,
      le_trans
        (Mettapedia.Logic.EvidenceDirichlet.idmLower_le_idmUpper ctx e i)
        (Mettapedia.Logic.EvidenceDirichlet.idmUpper_le_one ctx e i)⟩
  upper_in_unit := by
    exact ⟨
      Mettapedia.Logic.EvidenceDirichlet.idmUpper_nonneg ctx e i,
      Mettapedia.Logic.EvidenceDirichlet.idmUpper_le_one ctx e i⟩
  credibility_in_unit := by
    constructor
    · exact div_nonneg
        (by exact_mod_cast (Nat.zero_le e.total))
        (le_of_lt (Mettapedia.Logic.EvidenceDirichlet.idmDenom_pos ctx e))
    · apply (div_le_one
        (Mettapedia.Logic.EvidenceDirichlet.idmDenom_pos ctx e)).2
      change (e.total : ℝ) ≤ (e.total : ℝ) + ctx.s
      linarith [ctx.s_pos.le]

@[simp] theorem walleyCategoricalITV_credibility {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (walleyCategoricalITV ctx e i).credibility =
      (e.total : ℝ) /
        Mettapedia.Logic.EvidenceDirichlet.idmDenom ctx e :=
  rfl

/-- The raw categorical Walley-IDM ITV width is the existing
`EvidenceDirichlet.idmWidth` formula. -/
theorem walleyCategoricalITV_width_eq {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (walleyCategoricalITV ctx e i).width =
      Mettapedia.Logic.EvidenceDirichlet.idmWidth ctx e := by
  simpa [walleyCategoricalITV, ITV.width] using
    (Mettapedia.Logic.EvidenceDirichlet.idmWidth_eq_upper_sub_lower
      ctx e i).symm

/-- Categorical Walley-IDM also carries the width-complement law: imprecision
plus evidence precision is one. -/
theorem walleyCategoricalITV_width_add_credibility {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (walleyCategoricalITV ctx e i).width +
      (walleyCategoricalITV ctx e i).credibility = 1 := by
  rw [walleyCategoricalITV_width_eq, walleyCategoricalITV_credibility]
  unfold Mettapedia.Logic.EvidenceDirichlet.idmWidth
  have hden :
      Mettapedia.Logic.EvidenceDirichlet.idmDenom ctx e ≠ 0 :=
    ne_of_gt (Mettapedia.Logic.EvidenceDirichlet.idmDenom_pos ctx e)
  field_simp [hden]
  ring

/-- In a nondegenerate categorical carrier, the typed ITV width matches the
credal-set lower/upper envelope width for the queried category. -/
theorem walleyCategoricalITV_width_eq_credal_width_of_other {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (i j : Fin k) (hji : j ≠ i) :
    (walleyCategoricalITV ctx e i).width =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) -
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) := by
  rw [Mettapedia.Logic.WalleyMultinomialIDM.category_width_eq_EvidenceDirichlet_idmWidth_of_other
    (ctx := ctx) (e := e) (i := i) (j := j) (hji := hji)]
  exact walleyCategoricalITV_width_eq ctx e i

/-- Bayesian credible-interval semantics at fixed backend, prior context, and
credible level.  The source contains evidence plus the proof that the level is
admissible. -/
noncomputable def bayesCredibleITVSemantics
    (backend : Mettapedia.Logic.EvidenceBeta.CredibleIntervalBackend)
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
    (level : ℝ) : ITVSemantics where
  Source := BayesCredibleITVSource level
  toITV := fun src =>
    ITV.fromBayesCredibleWithBackend backend src.evidence ctx level src.level_ok

/-- Walley binary-IDM predictive semantics at fixed IDM strength `s`.  The
source contains evidence plus the proof that `s` is positive. -/
noncomputable def walleyBinaryITVSemantics (s : ℝ) : ITVSemantics where
  Source := WalleyBinaryITVSource s
  toITV := fun src => ITV.fromWalleyIDMPredictive src.evidence s src.s_pos

/-- Walley categorical-IDM predictive semantics at fixed IDM context and
outcome carrier size. -/
noncomputable def walleyCategoricalITVSemantics
    (k : ℕ) (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext) :
    ITVSemantics where
  Source := WalleyCategoricalITVSource k
  toITV := fun src => walleyCategoricalITV ctx src.evidence src.category

namespace TypedITV

/-- Tag a raw ITV with the generic semantics. -/
def fromGeneric (itv : ITV) : TypedITV genericITVSemantics :=
  ⟨itv⟩

/-- Build a typed Bayesian credible-interval ITV from evidence. -/
noncomputable def fromBayesCredible
    (backend : Mettapedia.Logic.EvidenceBeta.CredibleIntervalBackend)
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
    (level : ℝ) (hlevel : 0 < level ∧ level < 1)
    (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) :
    TypedITV (bayesCredibleITVSemantics backend ctx level) :=
  ⟨⟨e, hlevel⟩⟩

/-- Build a typed Walley binary-IDM ITV from evidence. -/
noncomputable def fromWalleyBinary
    (s : ℝ) (hs : 0 < s)
    (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) :
    TypedITV (walleyBinaryITVSemantics s) :=
  ⟨⟨e, hs⟩⟩

/-- Build a typed Walley categorical-IDM ITV from evidence and a queried
category. -/
noncomputable def fromWalleyCategorical {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    TypedITV (walleyCategoricalITVSemantics k ctx) :=
  ⟨⟨e, i⟩⟩

@[simp] theorem value_fromGeneric (itv : ITV) :
    (fromGeneric itv).value = itv :=
  rfl

@[simp] theorem value_fromBayesCredible
    (backend : Mettapedia.Logic.EvidenceBeta.CredibleIntervalBackend)
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
    (level : ℝ) (hlevel : 0 < level ∧ level < 1)
    (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) :
    (fromBayesCredible backend ctx level hlevel e).value =
      ITV.fromBayesCredibleWithBackend backend e ctx level hlevel :=
  rfl

@[simp] theorem value_fromWalleyBinary
    (s : ℝ) (hs : 0 < s)
    (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) :
    (fromWalleyBinary s hs e).value =
      ITV.fromWalleyIDMPredictive e s hs :=
  rfl

@[simp] theorem value_fromWalleyCategorical {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (fromWalleyCategorical ctx e i).value =
      walleyCategoricalITV ctx e i :=
  rfl

/-- Apply a raw unary operation while keeping its derived-operation provenance
visible in the result type. -/
noncomputable def applyUnary {Sem : ITVSemantics}
    (op : ITVUnaryOperation) (x : TypedITV Sem) :
    TypedITV (derivedUnaryITVSemantics Sem op) :=
  ⟨x⟩

/-- Apply a raw binary operation to same-semantics typed ITVs.  Cross-semantics
use requires an explicit bridge. -/
noncomputable def applyBinarySameSemantics {Sem : ITVSemantics}
    (op : ITVBinaryOperation) (x y : TypedITV Sem) :
    TypedITV (derivedBinaryITVSemantics Sem op) :=
  ⟨(x, y)⟩

/-- Typed negation, with operation provenance. -/
noncomputable def negation {Sem : ITVSemantics} (x : TypedITV Sem) :
    TypedITV (derivedUnaryITVSemantics Sem negationOperation) :=
  applyUnary negationOperation x

/-- Typed conjunction for same-semantics inputs. -/
noncomputable def conjunctionSameSemantics {Sem : ITVSemantics}
    (x y : TypedITV Sem) :
    TypedITV (derivedBinaryITVSemantics Sem conjunctionOperation) :=
  applyBinarySameSemantics conjunctionOperation x y

/-- Typed disjunction for same-semantics inputs. -/
noncomputable def disjunctionSameSemantics {Sem : ITVSemantics}
    (x y : TypedITV Sem) :
    TypedITV (derivedBinaryITVSemantics Sem disjunctionOperation) :=
  applyBinarySameSemantics disjunctionOperation x y

/-- Typed implication for same-semantics inputs. -/
noncomputable def implicationSameSemantics {Sem : ITVSemantics}
    (x y : TypedITV Sem) :
    TypedITV (derivedBinaryITVSemantics Sem implicationOperation) :=
  applyBinarySameSemantics implicationOperation x y

@[simp] theorem value_applyUnary {Sem : ITVSemantics}
    (op : ITVUnaryOperation) (x : TypedITV Sem) :
    (applyUnary op x).value = op.eval x.value :=
  rfl

@[simp] theorem value_applyBinarySameSemantics {Sem : ITVSemantics}
    (op : ITVBinaryOperation) (x y : TypedITV Sem) :
    (applyBinarySameSemantics op x y).value = op.eval x.value y.value :=
  rfl

@[simp] theorem value_negation {Sem : ITVSemantics} (x : TypedITV Sem) :
    (negation x).value = ITV.negation x.value :=
  rfl

@[simp] theorem value_conjunctionSameSemantics {Sem : ITVSemantics}
    (x y : TypedITV Sem) :
    (conjunctionSameSemantics x y).value = ITV.conjunction x.value y.value :=
  rfl

@[simp] theorem value_disjunctionSameSemantics {Sem : ITVSemantics}
    (x y : TypedITV Sem) :
    (disjunctionSameSemantics x y).value = ITV.disjunction x.value y.value :=
  rfl

@[simp] theorem value_implicationSameSemantics {Sem : ITVSemantics}
    (x y : TypedITV Sem) :
    (implicationSameSemantics x y).value = ITV.implication x.value y.value :=
  rfl

/-- An explicit bridge converts two source semantics into a shared target
semantics before a binary operation may combine them. -/
structure Bridge
    (Sem₁ : ITVSemantics.{u}) (Sem₂ : ITVSemantics.{v})
    (Target : ITVSemantics.{w}) where
  left : TypedITV Sem₁ → TypedITV Target
  right : TypedITV Sem₂ → TypedITV Target

/-- Forget constructor provenance into the generic raw-ITV semantics.  This is
always available, but it is an explicit bridge rather than a silent coercion. -/
noncomputable def forgetToGeneric {Sem : ITVSemantics}
    (x : TypedITV Sem) : TypedITV genericITVSemantics :=
  fromGeneric x.value

@[simp] theorem value_forgetToGeneric {Sem : ITVSemantics}
    (x : TypedITV Sem) :
    (forgetToGeneric x).value = x.value :=
  rfl

/-- The canonical explicit bridge that discards constructor provenance from two
possibly different source semantics. -/
noncomputable def genericBridge
    (Sem₁ : ITVSemantics.{u}) (Sem₂ : ITVSemantics.{v}) :
    Bridge Sem₁ Sem₂ genericITVSemantics where
  left := forgetToGeneric
  right := forgetToGeneric

/-- Apply a binary operation across two source semantics only after an explicit
bridge has converted both inputs to a shared target semantics. -/
noncomputable def applyBinaryViaBridge
    {Sem₁ Sem₂ Target : ITVSemantics} (op : ITVBinaryOperation)
    (B : Bridge Sem₁ Sem₂ Target) (x : TypedITV Sem₁) (y : TypedITV Sem₂) :
    TypedITV (derivedBinaryITVSemantics Target op) :=
  applyBinarySameSemantics op (B.left x) (B.right y)

/-- Conjunction across source semantics, via an explicit bridge. -/
noncomputable def conjunctionViaBridge
    {Sem₁ Sem₂ Target : ITVSemantics} (B : Bridge Sem₁ Sem₂ Target)
    (x : TypedITV Sem₁) (y : TypedITV Sem₂) :
    TypedITV (derivedBinaryITVSemantics Target conjunctionOperation) :=
  applyBinaryViaBridge conjunctionOperation B x y

@[simp] theorem value_applyBinaryViaBridge
    {Sem₁ Sem₂ Target : ITVSemantics} (op : ITVBinaryOperation)
    (B : Bridge Sem₁ Sem₂ Target) (x : TypedITV Sem₁) (y : TypedITV Sem₂) :
    (applyBinaryViaBridge op B x y).value =
      op.eval (B.left x).value (B.right y).value :=
  rfl

@[simp] theorem value_conjunctionViaBridge
    {Sem₁ Sem₂ Target : ITVSemantics} (B : Bridge Sem₁ Sem₂ Target)
    (x : TypedITV Sem₁) (y : TypedITV Sem₂) :
    (conjunctionViaBridge B x y).value =
      ITV.conjunction (B.left x).value (B.right y).value :=
  rfl

/-- The Walley binary typed constructor carries the width-complement law. -/
theorem walleyBinary_width_add_credibility
    (s : ℝ) (hs : 0 < s)
    (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) :
    (fromWalleyBinary s hs e).width +
      (fromWalleyBinary s hs e).credibility = 1 := by
  exact ITV.fromWalleyIDMPredictive_width_add_credibility e s hs

/-- The Walley categorical typed constructor carries the same
width-complement law as the binary slice. -/
theorem walleyCategorical_width_add_credibility {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (fromWalleyCategorical ctx e i).width +
      (fromWalleyCategorical ctx e i).credibility = 1 := by
  exact walleyCategoricalITV_width_add_credibility ctx e i

/-- The Walley categorical typed constructor's credibility is the IDM
precision proxy determined by total categorical evidence and IDM strength. -/
theorem walleyCategorical_credibility_eq {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (fromWalleyCategorical ctx e i).credibility =
      (e.total : ℝ) /
        Mettapedia.Logic.EvidenceDirichlet.idmDenom ctx e :=
  rfl

/-- In a nondegenerate categorical carrier, the typed Walley categorical ITV
width agrees with the corresponding credal-set lower/upper envelope width. -/
theorem walleyCategorical_width_eq_credal_width_of_other {k : ℕ}
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (i j : Fin k) (hji : j ≠ i) :
    (fromWalleyCategorical ctx e i).width =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) -
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) := by
  exact walleyCategoricalITV_width_eq_credal_width_of_other ctx e i j hji

/-- The Bayesian typed constructor keeps credibility tied to evidence
concentration and independent of interval backend internals. -/
theorem bayesCredible_credibility_eq
    (backend : Mettapedia.Logic.EvidenceBeta.CredibleIntervalBackend)
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
    (level : ℝ) (hlevel : 0 < level ∧ level < 1)
    (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) :
    (fromBayesCredible backend ctx level hlevel e).credibility =
      (Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toConfidence
        (ctx.α₀ + ctx.β₀) e).toReal := by
  exact ITV.fromBayesCredibleWithBackend_credibility backend e ctx level hlevel

/-- A same raw display can be available under different constructor semantics.
The type tag records which constructor semantics is being used; raw field
equality alone is not provenance equality. -/
theorem generic_and_walley_zero_can_share_raw_fields :
    let raw := ITV.fullWidthWithCredibility 0 (by norm_num)
    let generic : TypedITV genericITVSemantics := fromGeneric raw
    let walley : TypedITV (walleyBinaryITVSemantics 1) :=
      fromWalleyBinary 1 (by norm_num)
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero
    generic.lower = walley.lower ∧
      generic.upper = walley.upper ∧
        generic.credibility = walley.credibility := by
  dsimp [fromGeneric, fromWalleyBinary, value, lower, upper, credibility,
    genericITVSemantics, walleyBinaryITVSemantics,
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero]
  simp [ITV.fullWidthWithCredibility, ITV.fromWalleyIDMPredictive]

end TypedITV

/-! ## Forced queries versus chosen point projections -/

/-- If a query projection factors through a retained statistic, then equal
statistics force equal answers.  This is the generic "natural query" boundary:
what factors through the statistic is determined by it; anything else needs an
extra selector or model choice. -/
theorem forcedQuery_same_statistic_same_value
    {World Stat Val : Type*}
    (F : Mettapedia.Logic.PLNForcedQueries.ForcedByStatistic World Stat Val)
    {W₁ W₂ : World} (h : F.stat W₁ = F.stat W₂) :
    F.eval W₁ = F.eval W₂ :=
  Mettapedia.Logic.PLNForcedQueries.ForcedByStatistic.eval_eq_of_same_stat F h

/-- Binary world-model query strength is forced by extracted `BinaryEvidence`;
states with the same extracted evidence for a query cannot differ in strength
for that query. -/
theorem worldModel_queryStrength_forced_by_evidence
    {State Query : Type*}
    [Mettapedia.Logic.EvidenceClass.EvidenceType State]
    [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
    {W₁ W₂ : State} {q : Query}
    (h :
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₁ q =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₂ q) :
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength
        (State := State) (Query := Query) W₁ q =
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength
        (State := State) (Query := Query) W₂ q :=
  Mettapedia.Logic.PLNForcedQueries.queryStrength_eq_of_same_evidence h

/-- Binary world-model query confidence is forced by extracted
`BinaryEvidence` once the scale `κ` is fixed. -/
theorem worldModel_queryConfidence_forced_by_evidence
    {State Query : Type*}
    [Mettapedia.Logic.EvidenceClass.EvidenceType State]
    [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
    (κ : ℝ≥0∞) {W₁ W₂ : State} {q : Query}
    (h :
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₁ q =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₂ q) :
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryConfidence
        (State := State) (Query := Query) κ W₁ q =
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryConfidence
        (State := State) (Query := Query) κ W₂ q :=
  Mettapedia.Logic.PLNForcedQueries.queryConfidence_eq_of_same_evidence κ h

/-- Categorical sufficient-statistic surface query means are forced by the
aggregate `MultiEvidence`: two observation multisets with the same aggregate
evidence cannot differ in the selected category's empirical mean. -/
theorem categoricalSurface_queryMean_forced_by_aggregate
    {Obs Query : Type*} {k : ℕ}
    (S :
      Mettapedia.Logic.SufficientStatisticSurface Obs Query
        (Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k))
    {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k)
    (h :
      Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q) :
    ((Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q).counts i : ℝ) /
        ((Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q).total : ℝ) =
      ((Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q).counts i : ℝ) /
        ((Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q).total : ℝ) :=
  Mettapedia.Logic.PLNForcedQueries.categoricalSurface_mean_eq_of_same_aggregate
    S i h

/-- Categorical IDM lower, upper, and width projections are forced by the
aggregate `MultiEvidence` once the IDM context and category are chosen. -/
theorem categoricalSurface_idmEnvelope_forced_by_aggregate
    {Obs Query : Type*} {k : ℕ}
    (S :
      Mettapedia.Logic.SufficientStatisticSurface Obs Query
        (Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k))
    (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k)
    (h :
      Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q) :
    Mettapedia.Logic.EvidenceDirichlet.idmLower ctx
        (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q) i =
        Mettapedia.Logic.EvidenceDirichlet.idmLower ctx
          (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q) i ∧
      Mettapedia.Logic.EvidenceDirichlet.idmUpper ctx
        (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q) i =
        Mettapedia.Logic.EvidenceDirichlet.idmUpper ctx
          (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q) i ∧
      Mettapedia.Logic.EvidenceDirichlet.idmWidth ctx
        (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q) =
        Mettapedia.Logic.EvidenceDirichlet.idmWidth ctx
          (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q) :=
  ⟨
    Mettapedia.Logic.PLNForcedQueries.categoricalSurface_idmLower_eq_of_same_aggregate
      S ctx i h,
    Mettapedia.Logic.PLNForcedQueries.categoricalSurface_idmUpper_eq_of_same_aggregate
      S ctx i h,
    Mettapedia.Logic.PLNForcedQueries.categoricalSurface_idmWidth_eq_of_same_aggregate
      S ctx h
  ⟩

/-- Generic interval endpoints do not force a single point-valued projection:
lower, midpoint, and upper can all be distinct on the same ITV. -/
theorem genericITV_point_projection_not_forced :
    ∃ itv : ITV,
      Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ∧
        Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv ∧
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
            Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv :=
  Mettapedia.Logic.PLNForcedQueries.sameITV_has_three_distinct_selector_values

/-! ## Walley IDM bridge: an extra law that narrows coordinate freedom -/

/-- The explicit bridge law identifying the displayed confidence coordinate
with the complement of Walley's binary IDM predictive imprecision width. -/
def WidthComplementCompatible (χ : EvidenceWeightCoordinate) (s : ℝ) : Prop :=
  ∀ {n : ℝ}, 0 ≤ n → walleyPredictiveWidth n s + χ.encode n = 1

/-- PLN's odds coordinate is compatible with the binary IDM width-complement
bridge. -/
theorem plnOdds_widthComplementCompatible (s : ℝ) (hs : 0 < s) :
    WidthComplementCompatible (plnOddsCoordinate s hs) s := by
  intro n hn
  exact walley_width_add_plnOdds s hs hn

/-- The binary IDM width-complement bridge forces the PLN/NARS odds coordinate.

This theorem is the narrow forcing claim: the generic evidence-coordinate
space is large, but the selected Walley binary-predictive bridge collapses it
to `n / (n+s)`. -/
theorem widthComplementCompatible_forces_plnOdds
    (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s)
    (hχ : WidthComplementCompatible χ s)
    {n : ℝ} (hn : 0 ≤ n) :
    χ.encode n = (plnOddsCoordinate s hs).encode n :=
  walley_width_complement_forces_plnOdds χ s hs hχ hn

/-- A valid reconstructive coordinate can still fail the Walley-IDM bridge. -/
theorem reserveHalf_not_widthComplementCompatible
    (s : ℝ) (hs : 0 < s) :
    ¬ WidthComplementCompatible (reserveHalfCoordinate s hs) s :=
  reserveHalfCoordinate_not_walley_width_complement s hs

/-- A binary-IDM slice packages the evidence counts with Walley's strength
parameter `s`. -/
structure WalleyBinaryIDMSlice extends BinaryCounts where
  s : ℝ
  s_pos : 0 < s

namespace WalleyBinaryIDMSlice

/-- Walley's binary predictive interval width for this slice. -/
noncomputable def width (x : WalleyBinaryIDMSlice) : ℝ :=
  walleyPredictiveWidth x.total x.s

/-- The forced PLN/NARS confidence coordinate for this slice. -/
noncomputable def credibility (x : WalleyBinaryIDMSlice) : ℝ :=
  (plnOddsCoordinate x.s x.s_pos).encode x.total

/-- On the binary IDM bridge, width and PLN/NARS credibility are complements. -/
theorem width_add_credibility (x : WalleyBinaryIDMSlice) :
    x.width + x.credibility = 1 := by
  exact walley_width_add_plnOdds x.s x.s_pos x.toBinaryCounts.total_nonneg

/-- Any coordinate compatible with this slice's width-complement bridge agrees
with the forced PLN/NARS coordinate at the slice's total evidence. -/
theorem compatible_coordinate_eq_credibility
    (x : WalleyBinaryIDMSlice) (χ : EvidenceWeightCoordinate)
    (hχ : WidthComplementCompatible χ x.s) :
    χ.encode x.total = x.credibility := by
  exact widthComplementCompatible_forces_plnOdds χ x.s x.s_pos hχ x.toBinaryCounts.total_nonneg

end WalleyBinaryIDMSlice

/-! ## Credal/lower-prevision precision layer -/

/-- Source data for a raw ITV view obtained from a finite credal set.

The credal set and unit-bounded gamble force the lower/upper envelope.  The
credibility field is deliberately supplied separately: a credal envelope is an
imprecision object, while confidence is an evidence-concentration coordinate. -/
structure CredalEnvelopeITVSource (Ω : Type u) [Fintype Ω] where
  credal :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω
  gamble : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω
  credal_nonempty : credal.Nonempty
  gamble_in_unit : ∀ ω, gamble ω ∈ Set.Icc 0 1
  credibility : ℝ
  credibility_in_unit : credibility ∈ Set.Icc 0 1

/-- The ITV projection of a finite credal-set envelope with an explicitly
chosen credibility coordinate. -/
noncomputable def credalEnvelopeITV {Ω : Type u} [Fintype Ω]
    (src : CredalEnvelopeITVSource Ω) : ITV where
  lower :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
      src.credal src.gamble
  upper :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
      src.credal src.gamble
  credibility := src.credibility
  lower_le_upper :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb_le_upperProb_of_unit_gamble
      src.credal src.credal_nonempty src.gamble src.gamble_in_unit
  lower_in_unit :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb_mem_unit_of_unit_gamble
      src.credal src.credal_nonempty src.gamble src.gamble_in_unit
  upper_in_unit :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb_mem_unit_of_unit_gamble
      src.credal src.credal_nonempty src.gamble src.gamble_in_unit
  credibility_in_unit := src.credibility_in_unit

@[simp] theorem credalEnvelopeITV_lower {Ω : Type u} [Fintype Ω]
    (src : CredalEnvelopeITVSource Ω) :
    (credalEnvelopeITV src).lower =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        src.credal src.gamble :=
  rfl

@[simp] theorem credalEnvelopeITV_upper {Ω : Type u} [Fintype Ω]
    (src : CredalEnvelopeITVSource Ω) :
    (credalEnvelopeITV src).upper =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        src.credal src.gamble :=
  rfl

@[simp] theorem credalEnvelopeITV_credibility {Ω : Type u} [Fintype Ω]
    (src : CredalEnvelopeITVSource Ω) :
    (credalEnvelopeITV src).credibility = src.credibility :=
  rfl

/-- The typed semantics whose source is the full finite credal envelope data. -/
noncomputable def credalEnvelopeITVSemantics
    (Ω : Type u) [Fintype Ω] : ITVSemantics.{u} where
  Source := CredalEnvelopeITVSource Ω
  toITV := credalEnvelopeITV

namespace TypedITV

/-- Build a typed ITV from a finite credal-set envelope. -/
noncomputable def fromCredalEnvelope {Ω : Type u} [Fintype Ω]
    (src : CredalEnvelopeITVSource Ω) :
    TypedITV (credalEnvelopeITVSemantics Ω) :=
  ⟨src⟩

@[simp] theorem value_fromCredalEnvelope {Ω : Type u} [Fintype Ω]
    (src : CredalEnvelopeITVSource Ω) :
    (fromCredalEnvelope src).value = credalEnvelopeITV src :=
  by simp [fromCredalEnvelope, TypedITV.value, credalEnvelopeITVSemantics]

@[simp] theorem fromCredalEnvelope_lower {Ω : Type u} [Fintype Ω]
    (src : CredalEnvelopeITVSource Ω) :
    (fromCredalEnvelope src).lower =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        src.credal src.gamble :=
  by simp [fromCredalEnvelope, TypedITV.lower, TypedITV.value,
    credalEnvelopeITVSemantics, credalEnvelopeITV]

@[simp] theorem fromCredalEnvelope_upper {Ω : Type u} [Fintype Ω]
    (src : CredalEnvelopeITVSource Ω) :
    (fromCredalEnvelope src).upper =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        src.credal src.gamble :=
  by simp [fromCredalEnvelope, TypedITV.upper, TypedITV.value,
    credalEnvelopeITVSemantics, credalEnvelopeITV]

@[simp] theorem fromCredalEnvelope_credibility {Ω : Type u} [Fintype Ω]
    (src : CredalEnvelopeITVSource Ω) :
    (fromCredalEnvelope src).credibility = src.credibility :=
  by simp [fromCredalEnvelope, TypedITV.credibility, TypedITV.value,
    credalEnvelopeITVSemantics, credalEnvelopeITV]

end TypedITV

/-! ### Projective credal envelopes as width-complement ITVs -/

/-- Source data for the PLN interval view obtained from a projective global
credal envelope under the width-complement convention.

Unlike `CredalEnvelopeITVSource`, this source does not allow an arbitrary
credibility coordinate: the credibility is specifically the complement of the
compatible-completion envelope width.  This is a named bridge law, not a generic
fact about every credal interval. -/
structure ProjectiveCredalWidthComplementITVSource
    (Window : Type u) (Global : Type v) [LE Window] where
  spec : ProjectiveLocalCredalSpec.{u, v} Window Global
  compatible : spec.hasCompatibleCompletion
  gamble : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Global
  gamble_in_unit : ∀ ω, gamble ω ∈ Set.Icc (0 : ℝ) 1
  bddBelow :
    BddBelow ((fun P : PrecisePrevision Global => P gamble) ''
      spec.projectiveLimitCredalSet)
  bddAbove :
    BddAbove ((fun P : PrecisePrevision Global => P gamble) ''
      spec.projectiveLimitCredalSet)

namespace ProjectiveCredalWidthComplementITVSource

/-- In finite global state spaces, boundedness of the projective credal range is
automatic, so the source only needs the coherent-completion and unit-gamble
gates. -/
noncomputable def finite
    {Window : Type u} {Global : Type v} [LE Window] [Fintype Global] [Nonempty Global]
    (spec : ProjectiveLocalCredalSpec.{u, v} Window Global)
    (compatible : spec.hasCompatibleCompletion)
    (gamble : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Global)
    (gamble_in_unit : ∀ ω, gamble ω ∈ Set.Icc (0 : ℝ) 1) :
    ProjectiveCredalWidthComplementITVSource Window Global where
  spec := spec
  compatible := compatible
  gamble := gamble
  gamble_in_unit := gamble_in_unit
  bddBelow := finite_credalRange_bddBelow spec.projectiveLimitCredalSet gamble
  bddAbove := finite_credalRange_bddAbove spec.projectiveLimitCredalSet gamble

end ProjectiveCredalWidthComplementITVSource

/-- Projective lower/upper envelope compressed to an ITV by the
width-complement law. -/
noncomputable def projectiveCredalWidthComplementITV
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) : ITV where
  lower := src.spec.globalNaturalExtension src.gamble
  upper := upperEnvelope src.spec.projectiveLimitCredalSet src.gamble
  credibility := src.spec.globalEnvelopeWidthComplement src.gamble
  lower_le_upper :=
    lowerEnvelope_le_upperEnvelope_of_nonempty src.spec.projectiveLimitCredalSet
      src.gamble src.compatible src.bddBelow src.bddAbove
  lower_in_unit :=
    lowerEnvelope_in_unit_of_unit src.spec.projectiveLimitCredalSet src.gamble
      src.compatible src.bddBelow src.gamble_in_unit
  upper_in_unit :=
    upperEnvelope_in_unit_of_unit src.spec.projectiveLimitCredalSet src.gamble
      src.compatible src.bddAbove src.gamble_in_unit
  credibility_in_unit :=
    src.spec.globalEnvelopeWidthComplement_in_unit_of_unit src.compatible
      src.gamble src.bddBelow src.bddAbove src.gamble_in_unit

@[simp] theorem projectiveCredalWidthComplementITV_lower
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (projectiveCredalWidthComplementITV src).lower =
      src.spec.globalNaturalExtension src.gamble :=
  rfl

@[simp] theorem projectiveCredalWidthComplementITV_upper
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (projectiveCredalWidthComplementITV src).upper =
      upperEnvelope src.spec.projectiveLimitCredalSet src.gamble :=
  rfl

@[simp] theorem projectiveCredalWidthComplementITV_credibility
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (projectiveCredalWidthComplementITV src).credibility =
      src.spec.globalEnvelopeWidthComplement src.gamble :=
  rfl

@[simp] theorem projectiveCredalWidthComplementITV_width
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (projectiveCredalWidthComplementITV src).width =
      src.spec.globalEnvelopeWidth src.gamble := by
  rfl

@[simp] theorem projectiveCredalWidthComplementITV_strength
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (projectiveCredalWidthComplementITV src).strength =
      src.spec.globalEnvelopeMidpoint src.gamble := by
  rfl

/-- The projective width-complement bridge makes ITV width plus credibility add
to one. -/
theorem projectiveCredalWidthComplementITV_width_add_credibility
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (projectiveCredalWidthComplementITV src).width +
        (projectiveCredalWidthComplementITV src).credibility = 1 := by
  simp [projectiveCredalWidthComplementITV, ITV.width,
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    ProjectiveLocalCredalSpec.globalNaturalExtension,
    credalEnvelopeWidth, credalEnvelopeWidthComplement]

/-- The typed semantics for projective credal envelopes with the
width-complement credibility convention. -/
noncomputable def projectiveCredalWidthComplementITVSemantics
    (Window : Type u) (Global : Type v) [LE Window] :
    ITVSemantics.{max u (v + 1)} where
  Source := ProjectiveCredalWidthComplementITVSource.{u, v} Window Global
  toITV := projectiveCredalWidthComplementITV

namespace TypedITV

/-- Build a typed ITV from a projective credal envelope under the
width-complement bridge law. -/
noncomputable def fromProjectiveCredalWidthComplement
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    TypedITV (projectiveCredalWidthComplementITVSemantics.{u, v} Window Global) :=
  ⟨src⟩

@[simp] theorem value_fromProjectiveCredalWidthComplement
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (fromProjectiveCredalWidthComplement src).value =
      projectiveCredalWidthComplementITV src := by
  simp [fromProjectiveCredalWidthComplement, TypedITV.value,
    projectiveCredalWidthComplementITVSemantics]

@[simp] theorem fromProjectiveCredalWidthComplement_lower
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (fromProjectiveCredalWidthComplement src).lower =
      src.spec.globalNaturalExtension src.gamble := by
  simp [fromProjectiveCredalWidthComplement, TypedITV.lower, TypedITV.value,
    projectiveCredalWidthComplementITVSemantics,
    projectiveCredalWidthComplementITV]

@[simp] theorem fromProjectiveCredalWidthComplement_upper
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (fromProjectiveCredalWidthComplement src).upper =
      upperEnvelope src.spec.projectiveLimitCredalSet src.gamble := by
  simp [fromProjectiveCredalWidthComplement, TypedITV.upper, TypedITV.value,
    projectiveCredalWidthComplementITVSemantics,
    projectiveCredalWidthComplementITV]

@[simp] theorem fromProjectiveCredalWidthComplement_credibility
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (fromProjectiveCredalWidthComplement src).credibility =
      src.spec.globalEnvelopeWidthComplement src.gamble := by
  simp [fromProjectiveCredalWidthComplement, TypedITV.credibility,
    TypedITV.value, projectiveCredalWidthComplementITVSemantics,
    projectiveCredalWidthComplementITV]

@[simp] theorem fromProjectiveCredalWidthComplement_width
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (fromProjectiveCredalWidthComplement src).width =
      src.spec.globalEnvelopeWidth src.gamble := by
  simp [fromProjectiveCredalWidthComplement, TypedITV.width, TypedITV.value,
    projectiveCredalWidthComplementITVSemantics]

@[simp] theorem fromProjectiveCredalWidthComplement_midpoint
    {Window : Type u} {Global : Type v} [LE Window]
    (src : ProjectiveCredalWidthComplementITVSource.{u, v} Window Global) :
    (fromProjectiveCredalWidthComplement src).midpoint =
      src.spec.globalEnvelopeMidpoint src.gamble := by
  simp [fromProjectiveCredalWidthComplement, TypedITV.midpoint, TypedITV.value,
    projectiveCredalWidthComplementITVSemantics]

end TypedITV

/-- A finite credal envelope fixes lower/upper bounds but does not determine
the credibility coordinate. -/
theorem credalEnvelope_bounds_do_not_force_credibility
    {Ω : Type u} [Fintype Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    let x : TypedITV (credalEnvelopeITVSemantics Ω) :=
      TypedITV.fromCredalEnvelope
        { credal := K
          gamble := f
          credal_nonempty := hK
          gamble_in_unit := hf
          credibility := 0
          credibility_in_unit := by norm_num }
    let y : TypedITV (credalEnvelopeITVSemantics Ω) :=
      TypedITV.fromCredalEnvelope
        { credal := K
          gamble := f
          credal_nonempty := hK
          gamble_in_unit := hf
          credibility := 1
          credibility_in_unit := by norm_num }
    x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility := by
  dsimp
  norm_num

/-! ## Abstract lower-prevision ITV views -/

/-- Every coherent lower prevision is below its conjugate upper prevision on
the same gamble. -/
theorem lowerPrevision_le_conjugate
    {Ω : Type u}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    P X ≤ P.conjugate X := by
  have h :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision_nonneg P X
  dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision] at h
  linarith

/-- The conjugate upper prevision of a unit-bounded gamble is at most one. -/
theorem lowerPrevision_conjugate_le_one_of_unit
    {Ω : Type u}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    P.conjugate X ≤ 1 := by
  have hbound : ∀ ω, (-1 : ℝ) ≤ (-X) ω := by
    intro ω
    exact neg_le_neg ((hX ω).2)
  have hP : (-1 : ℝ) ≤ P (-X) := P.lower_bound (-X) (-1) hbound
  dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision.conjugate]
  linarith

/-- Source data for a raw ITV view obtained from an abstract coherent lower
prevision.

The lower prevision and unit-bounded gamble force the lower endpoint and the
conjugate upper endpoint.  The credibility coordinate is supplied separately,
because evidence concentration is not a function of lower/upper imprecision in
general. -/
structure LowerPrevisionITVSource (Ω : Type u) where
  prevision : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω
  gamble : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω
  gamble_in_unit : ∀ ω, gamble ω ∈ Set.Icc 0 1
  credibility : ℝ
  credibility_in_unit : credibility ∈ Set.Icc 0 1

/-- The lower endpoint forced by an abstract lower prevision lies in `[0,1]`
for unit-bounded gambles. -/
theorem LowerPrevisionITVSource.lower_in_unit
    {Ω : Type u} (src : LowerPrevisionITVSource Ω) :
    src.prevision src.gamble ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact src.prevision.nonneg_of_nonneg (fun ω => (src.gamble_in_unit ω).1)
  · exact
      (lowerPrevision_le_conjugate src.prevision src.gamble).trans
        (lowerPrevision_conjugate_le_one_of_unit src.prevision src.gamble
          src.gamble_in_unit)

/-- The conjugate upper endpoint forced by an abstract lower prevision lies in
`[0,1]` for unit-bounded gambles. -/
theorem LowerPrevisionITVSource.upper_in_unit
    {Ω : Type u} (src : LowerPrevisionITVSource Ω) :
    src.prevision.conjugate src.gamble ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact
      (src.prevision.nonneg_of_nonneg (fun ω => (src.gamble_in_unit ω).1)).trans
        (lowerPrevision_le_conjugate src.prevision src.gamble)
  · exact lowerPrevision_conjugate_le_one_of_unit src.prevision src.gamble
      src.gamble_in_unit

/-- The ITV projection of an abstract lower prevision with an explicitly chosen
credibility coordinate. -/
noncomputable def lowerPrevisionITV {Ω : Type u}
    (src : LowerPrevisionITVSource Ω) : ITV where
  lower := src.prevision src.gamble
  upper := src.prevision.conjugate src.gamble
  credibility := src.credibility
  lower_le_upper := lowerPrevision_le_conjugate src.prevision src.gamble
  lower_in_unit := src.lower_in_unit
  upper_in_unit := src.upper_in_unit
  credibility_in_unit := src.credibility_in_unit

@[simp] theorem lowerPrevisionITV_lower {Ω : Type u}
    (src : LowerPrevisionITVSource Ω) :
    (lowerPrevisionITV src).lower = src.prevision src.gamble :=
  rfl

@[simp] theorem lowerPrevisionITV_upper {Ω : Type u}
    (src : LowerPrevisionITVSource Ω) :
    (lowerPrevisionITV src).upper = src.prevision.conjugate src.gamble :=
  rfl

@[simp] theorem lowerPrevisionITV_credibility {Ω : Type u}
    (src : LowerPrevisionITVSource Ω) :
    (lowerPrevisionITV src).credibility = src.credibility :=
  rfl

/-- The typed semantics whose source is an abstract lower prevision plus the
queried gamble. -/
noncomputable def lowerPrevisionITVSemantics
    (Ω : Type u) : ITVSemantics.{u} where
  Source := LowerPrevisionITVSource Ω
  toITV := lowerPrevisionITV

namespace TypedITV

/-- Build a typed ITV from an abstract lower-prevision envelope. -/
noncomputable def fromLowerPrevision {Ω : Type u}
    (src : LowerPrevisionITVSource Ω) :
    TypedITV (lowerPrevisionITVSemantics Ω) :=
  ⟨src⟩

@[simp] theorem value_fromLowerPrevision {Ω : Type u}
    (src : LowerPrevisionITVSource Ω) :
    (fromLowerPrevision src).value = lowerPrevisionITV src :=
  by simp [fromLowerPrevision, TypedITV.value, lowerPrevisionITVSemantics]

@[simp] theorem fromLowerPrevision_lower {Ω : Type u}
    (src : LowerPrevisionITVSource Ω) :
    (fromLowerPrevision src).lower = src.prevision src.gamble :=
  by simp [fromLowerPrevision, TypedITV.lower, TypedITV.value,
    lowerPrevisionITVSemantics, lowerPrevisionITV]

@[simp] theorem fromLowerPrevision_upper {Ω : Type u}
    (src : LowerPrevisionITVSource Ω) :
    (fromLowerPrevision src).upper = src.prevision.conjugate src.gamble :=
  by simp [fromLowerPrevision, TypedITV.upper, TypedITV.value,
    lowerPrevisionITVSemantics, lowerPrevisionITV]

@[simp] theorem fromLowerPrevision_credibility {Ω : Type u}
    (src : LowerPrevisionITVSource Ω) :
    (fromLowerPrevision src).credibility = src.credibility :=
  by simp [fromLowerPrevision, TypedITV.credibility, TypedITV.value,
    lowerPrevisionITVSemantics, lowerPrevisionITV]

end TypedITV

/-- An abstract lower-prevision envelope fixes lower/upper bounds but does not
determine the credibility coordinate. -/
theorem lowerPrevision_bounds_do_not_force_credibility
    {Ω : Type u}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    let x : TypedITV (lowerPrevisionITVSemantics Ω) :=
      TypedITV.fromLowerPrevision
        { prevision := P
          gamble := X
          gamble_in_unit := hX
          credibility := 0
          credibility_in_unit := by norm_num }
    let y : TypedITV (lowerPrevisionITVSemantics Ω) :=
      TypedITV.fromLowerPrevision
        { prevision := P
          gamble := X
          gamble_in_unit := hX
          credibility := 1
          credibility_in_unit := by norm_num }
    x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility := by
  dsimp
  norm_num

/-! ## Precise singleton-credal bridge into lower-prevision ITVs -/

namespace SingletonCredalLowerPrevision

open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-- Expected value is positively homogeneous in the gamble. -/
theorem expectedValue_smul
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω) (r : ℝ) (X : Gamble Ω) :
    expectedValue P (r • X) = r * expectedValue P X := by
  unfold expectedValue
  calc
    (∑ ω : Ω, P.prob ω * (r • X) ω) =
        ∑ ω : Ω, r * (P.prob ω * X ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      simp [mul_assoc, mul_comm]
    _ = r * ∑ ω : Ω, P.prob ω * X ω := by
      rw [Finset.mul_sum]

/-- Expected value of a negated gamble is the negated expected value. -/
theorem expectedValue_neg
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω) (X : Gamble Ω) :
    expectedValue P (-X) = -expectedValue P X := by
  simpa using expectedValue_smul P (-1 : ℝ) X

/-- Expected value respects pointwise lower bounds. -/
theorem expectedValue_lower_bound
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω) (X : Gamble Ω) (c : ℝ)
    (hc : ∀ ω, c ≤ X ω) :
    c ≤ expectedValue P X := by
  unfold expectedValue
  calc
    c = (∑ ω : Ω, P.prob ω) * c := by rw [P.sum_one]; ring
    _ = ∑ ω : Ω, P.prob ω * c := by rw [Finset.sum_mul]
    _ ≤ ∑ ω : Ω, P.prob ω * X ω := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hc ω) (P.non_neg ω)

/-- A precise probability distribution induces a coherent lower prevision by
ordinary expectation.  This is the singleton-credal special case of the lower
envelope construction. -/
noncomputable def probDistLowerPrevision
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω where
  toFun := fun X => expectedValue P X
  lower_bound := expectedValue_lower_bound P
  pos_homog := by
    intro r X _hr
    exact expectedValue_smul P r X
  superadd := by
    intro X Y
    exact le_of_eq (expectedValue_add P X Y).symm

@[simp] theorem probDistLowerPrevision_apply
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    probDistLowerPrevision P X = expectedValue P X :=
  rfl

@[simp] theorem probDistLowerPrevision_conjugate_apply
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    (probDistLowerPrevision P).conjugate X = expectedValue P X := by
  dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision.conjugate,
    probDistLowerPrevision]
  rw [show expectedValue P (-X) = -expectedValue P X from expectedValue_neg P X]
  ring

/-- The lower-prevision source associated with a singleton precise
distribution. -/
noncomputable def source
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω) (X : Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    LowerPrevisionITVSource Ω where
  prevision := probDistLowerPrevision P
  gamble := X
  gamble_in_unit := hX
  credibility := credibility
  credibility_in_unit := hc

/-- The finite singleton-credal envelope source with the same query and
credibility coordinate. -/
noncomputable def credalEnvelopeSource
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω) (X : Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    CredalEnvelopeITVSource Ω where
  credal := Set.singleton P
  gamble := X
  credal_nonempty := ⟨P, rfl⟩
  gamble_in_unit := hX
  credibility := credibility
  credibility_in_unit := hc

/-- For a singleton credal set, the lower-prevision ITV view and finite
credal-envelope ITV view agree on both forced endpoints and on the selected
credibility coordinate. -/
theorem typedLowerPrevision_agrees_with_singletonCredalEnvelope
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω) (X : Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let lp : TypedITV (lowerPrevisionITVSemantics Ω) :=
      TypedITV.fromLowerPrevision (source P X hX credibility hc);
    let ce : TypedITV (credalEnvelopeITVSemantics Ω) :=
      TypedITV.fromCredalEnvelope (credalEnvelopeSource P X hX credibility hc);
    lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
      lp.credibility = ce.credibility := by
  dsimp
  constructor
  · dsimp [TypedITV.lower, TypedITV.value, lowerPrevisionITVSemantics,
      credalEnvelopeITVSemantics, lowerPrevisionITV, credalEnvelopeITV,
      TypedITV.fromLowerPrevision, TypedITV.fromCredalEnvelope, source,
      credalEnvelopeSource]
    rw [lowerProb_singleton_eq_expectedValue]
  constructor
  · dsimp [TypedITV.upper, TypedITV.value, lowerPrevisionITVSemantics,
      credalEnvelopeITVSemantics, lowerPrevisionITV, credalEnvelopeITV,
      TypedITV.fromLowerPrevision, TypedITV.fromCredalEnvelope, source,
      credalEnvelopeSource]
    rw [probDistLowerPrevision_conjugate_apply, upperProb_singleton_eq_expectedValue]
  · rfl

end SingletonCredalLowerPrevision

/-! ## Finite credal sets as lower-prevision sources -/

namespace FiniteCredalLowerPrevision

open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-- A finite probability mass is bounded above by one. -/
theorem prob_le_one
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω) (ω : Ω) :
    P.prob ω ≤ 1 := by
  calc
    P.prob ω ≤ ∑ x : Ω, P.prob x :=
      Finset.single_le_sum (fun x _ => P.non_neg x) (Finset.mem_univ ω)
    _ = 1 := P.sum_one

/-- Expected values over finite probability distributions are bounded below by
the negative `ℓ₁` size of the gamble. -/
theorem expectedValue_ge_neg_sum_abs
    {Ω : Type u} [Fintype Ω]
    (P : ProbDist Ω) (X : Gamble Ω) :
    -(∑ ω : Ω, |X ω|) ≤ expectedValue P X := by
  unfold expectedValue
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have habs : 0 ≤ |X ω| := abs_nonneg (X ω)
  have hp0 : 0 ≤ P.prob ω := P.non_neg ω
  have hp1 : P.prob ω ≤ 1 := prob_le_one P ω
  have hscale : -|X ω| ≤ P.prob ω * (-|X ω|) := by
    have hm : P.prob ω * |X ω| ≤ 1 * |X ω| :=
      mul_le_mul_of_nonneg_right hp1 habs
    have hn := neg_le_neg hm
    simpa [mul_neg, one_mul] using hn
  have hx : -|X ω| ≤ X ω := neg_abs_le (X ω)
  exact hscale.trans (mul_le_mul_of_nonneg_left hx hp0)

/-- The expectation image of a finite credal set is bounded below for every
gamble. -/
theorem expectedValue_image_bddBelow
    {Ω : Type u} [Fintype Ω]
    (K : CredalSetFinite Ω) (X : Gamble Ω) :
    BddBelow (Set.image (fun P => expectedValue P X) K) := by
  refine ⟨-(∑ ω : Ω, |X ω|), ?_⟩
  intro y hy
  rcases hy with ⟨P, _hP, rfl⟩
  exact expectedValue_ge_neg_sum_abs P X

/-- Finite credal lower probability is positively homogeneous. -/
theorem lowerProb_smul_of_nonneg
    {Ω : Type u} [Fintype Ω]
    (K : CredalSetFinite Ω) (r : ℝ) (hr : 0 ≤ r) (X : Gamble Ω) :
    lowerProb K (r • X) = r * lowerProb K X := by
  unfold lowerProb
  have hset :
      Set.image (fun P => expectedValue P (r • X)) K =
        r • Set.image (fun P => expectedValue P X) K := by
    ext y
    constructor
    · rintro ⟨P, hP, rfl⟩
      rw [Set.mem_smul_set]
      refine ⟨expectedValue P X, ⟨P, hP, rfl⟩, ?_⟩
      simp [SingletonCredalLowerPrevision.expectedValue_smul]
    · intro hy
      rw [Set.mem_smul_set] at hy
      rcases hy with ⟨z, ⟨P, hP, hz⟩, hyz⟩
      refine ⟨P, hP, ?_⟩
      subst z
      simpa [SingletonCredalLowerPrevision.expectedValue_smul] using hyz
  rw [hset, Real.sInf_smul_of_nonneg (a := r) hr]
  rfl

/-- The finite credal lower envelope as a coherent lower prevision. -/
noncomputable def credalLowerPrevision
    {Ω : Type u} [Fintype Ω]
    (K : CredalSetFinite Ω) (hK : K.Nonempty) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω where
  toFun := fun X => lowerProb K X
  lower_bound := by
    intro X c hc
    unfold lowerProb
    have hS_ne :
        (Set.image (fun P => expectedValue P X) K).Nonempty := by
      rcases hK with ⟨P, hP⟩
      exact ⟨expectedValue P X, ⟨P, hP, rfl⟩⟩
    apply le_csInf hS_ne
    intro y hy
    rcases hy with ⟨P, _hP, rfl⟩
    exact SingletonCredalLowerPrevision.expectedValue_lower_bound P X c hc
  pos_homog := by
    intro r X hr
    exact lowerProb_smul_of_nonneg K r hr X
  superadd := by
    intro X Y
    exact lowerProb_superadditive K hK X Y
      (expectedValue_image_bddBelow K X)
      (expectedValue_image_bddBelow K Y)
      (expectedValue_image_bddBelow K (X + Y))

@[simp] theorem credalLowerPrevision_apply
    {Ω : Type u} [Fintype Ω]
    (K : CredalSetFinite Ω) (hK : K.Nonempty) (X : Gamble Ω) :
    credalLowerPrevision K hK X = lowerProb K X :=
  rfl

/-- The conjugate of the finite credal lower prevision is the finite credal
upper envelope. -/
theorem credalLowerPrevision_conjugate_apply
    {Ω : Type u} [Fintype Ω]
    (K : CredalSetFinite Ω) (hK : K.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    (credalLowerPrevision K hK).conjugate X = upperProb K X := by
  dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision.conjugate,
    credalLowerPrevision, lowerProb, upperProb]
  have hset :
      Set.image (fun P => expectedValue P (-X)) K =
        -Set.image (fun P => expectedValue P X) K := by
    ext y
    constructor
    · rintro ⟨P, hP, rfl⟩
      rw [Set.mem_neg]
      refine ⟨P, hP, ?_⟩
      simp only []
      rw [show expectedValue P (-X) = -expectedValue P X from
        SingletonCredalLowerPrevision.expectedValue_neg P X]
      ring
    · intro hy
      rw [Set.mem_neg] at hy
      rcases hy with ⟨P, hP, hy⟩
      refine ⟨P, hP, ?_⟩
      simp only [] at hy ⊢
      rw [show expectedValue P (-X) = -expectedValue P X from
        SingletonCredalLowerPrevision.expectedValue_neg P X, hy]
      ring
  rw [hset, Real.sInf_neg]
  ring

/-- The lower-prevision source associated with a finite credal set. -/
noncomputable def source
    {Ω : Type u} [Fintype Ω]
    (K : CredalSetFinite Ω) (hK : K.Nonempty) (X : Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    LowerPrevisionITVSource Ω where
  prevision := credalLowerPrevision K hK
  gamble := X
  gamble_in_unit := hX
  credibility := credibility
  credibility_in_unit := hc

/-- For finite credal sets, the lower-prevision ITV view and finite
credal-envelope ITV view agree on both forced endpoints and on the selected
credibility coordinate. -/
theorem typedLowerPrevision_agrees_with_credalEnvelope
    {Ω : Type u} [Fintype Ω]
    (K : CredalSetFinite Ω) (hK : K.Nonempty) (X : Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let lp : TypedITV (lowerPrevisionITVSemantics Ω) :=
      TypedITV.fromLowerPrevision (source K hK X hX credibility hc);
    let ce : TypedITV (credalEnvelopeITVSemantics Ω) :=
      TypedITV.fromCredalEnvelope
        { credal := K
          gamble := X
          credal_nonempty := hK
          gamble_in_unit := hX
          credibility := credibility
          credibility_in_unit := hc };
    lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
      lp.credibility = ce.credibility := by
  dsimp
  constructor
  · rfl
  constructor
  · dsimp [TypedITV.upper, TypedITV.value, lowerPrevisionITVSemantics,
      credalEnvelopeITVSemantics, lowerPrevisionITV, credalEnvelopeITV,
      TypedITV.fromLowerPrevision, TypedITV.fromCredalEnvelope, source]
    rw [credalLowerPrevision_conjugate_apply]
  · rfl

end FiniteCredalLowerPrevision

/-! ## Finite desirable-gamble natural extension -/

namespace DesirableLowerPrevisionBridge

open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-- Finite pointwise minimum of a gamble on a nonempty finite outcome space. -/
noncomputable def finiteMinimum
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] (X : Gamble Ω) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty X

theorem finiteMinimum_le_apply
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] (X : Gamble Ω) (ω : Ω) :
    finiteMinimum X ≤ X ω :=
  Finset.inf'_le X (Finset.mem_univ ω)

theorem exists_apply_eq_finiteMinimum
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] (X : Gamble Ω) :
    ∃ ω, X ω = finiteMinimum X := by
  obtain ⟨ω₀, _hω₀_mem, hω₀_min⟩ :=
    Finset.exists_min_image Finset.univ X Finset.univ_nonempty
  refine ⟨ω₀, ?_⟩
  symm
  apply le_antisymm
  · exact finiteMinimum_le_apply X ω₀
  · apply Finset.le_inf'
    intro ω _
    exact hω₀_min ω (Finset.mem_univ ω)

/-- The scalar set whose supremum defines the lower prevision induced by a
coherent desirable-gamble set.

`α` is acceptable exactly when buying `X` for price `α` leaves a desirable
gamble. -/
noncomputable def acceptablePrices
    {Ω : Type u}
    (C : CoherentDesirableSet Ω) (X : Gamble Ω) : Set ℝ :=
  {α : ℝ | (X - (fun _ => α)) ∈ C.D}

@[simp] theorem acceptablePrices_mem
    {Ω : Type u}
    (C : CoherentDesirableSet Ω) (X : Gamble Ω) (α : ℝ) :
    α ∈ acceptablePrices C X ↔ (X - (fun _ => α)) ∈ C.D :=
  Iff.rfl

/-- On a finite nonempty outcome space, the acceptable price set is nonempty:
any price strictly below the finite minimum of the gamble leaves a sure gain. -/
theorem acceptablePrices_nonempty
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C : CoherentDesirableSet Ω) (X : Gamble Ω) :
    (acceptablePrices C X).Nonempty := by
  let m := Finset.univ.inf' Finset.univ_nonempty X
  refine ⟨m - 1, ?_⟩
  dsimp [acceptablePrices]
  apply C.D2
  intro ω
  have hm : m ≤ X ω := Finset.inf'_le X (Finset.mem_univ ω)
  dsimp
  linarith

/-- On a finite nonempty outcome space, the acceptable price set is bounded
above by the finite maximum of the gamble.  Otherwise the residual gamble would
be strictly negative everywhere, contradicting desirable-gamble coherence. -/
theorem acceptablePrices_bddAbove
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C : CoherentDesirableSet Ω) (X : Gamble Ω) :
    BddAbove (acceptablePrices C X) := by
  let M := Finset.univ.sup' Finset.univ_nonempty X
  refine ⟨M, ?_⟩
  intro α hα
  by_contra hnot
  have hlt : M < α := lt_of_not_ge hnot
  have hneg : Gamble.StrictlyNegative (X - (fun _ => α)) := by
    intro ω
    have hXle : X ω ≤ M := Finset.le_sup' X (Finset.mem_univ ω)
    dsimp
    linarith
  exact avoid_sure_loss C (X - (fun _ => α)) hneg hα

/-- The induced lower prevision satisfies Walley's lower-bound axiom on finite
nonempty outcome spaces.

The non-strict boundary price is recovered as the supremum of all strictly
lower acceptable prices. -/
theorem lowerPrevision_lower_bound
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C : CoherentDesirableSet Ω) (X : Gamble Ω) (c : ℝ)
    (hc : ∀ ω, c ≤ X ω) :
    c ≤
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X := by
  change c ≤ sSup (acceptablePrices C X)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hmem : c - ε ∈ acceptablePrices C X := by
    apply C.D2
    intro ω
    have hcx := hc ω
    dsimp
    linarith
  have hle := le_csSup (acceptablePrices_bddAbove C X) hmem
  linarith

/-- The zero gamble has induced lower prevision zero. -/
theorem lowerPrevision_zero
    {Ω : Type u}
    (C : CoherentDesirableSet Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      C (0 : Gamble Ω) = 0 := by
  change sSup (acceptablePrices C (0 : Gamble Ω)) = 0
  apply le_antisymm
  · apply csSup_le
    · refine ⟨-1, ?_⟩
      apply C.D2
      intro ω
      dsimp
      norm_num
    · intro α hα
      by_contra hnot
      have hαpos : 0 < α := lt_of_not_ge hnot
      have hneg : Gamble.StrictlyNegative ((0 : Gamble Ω) - (fun _ => α)) := by
        intro ω
        dsimp
        linarith
      exact avoid_sure_loss C ((0 : Gamble Ω) - (fun _ => α)) hneg hα
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hmem : -ε ∈ acceptablePrices C (0 : Gamble Ω) := by
      apply C.D2
      intro ω
      dsimp
      linarith
    have hbdd : BddAbove (acceptablePrices C (0 : Gamble Ω)) := by
      refine ⟨0, ?_⟩
      intro α hα
      by_contra hnot
      have hαpos : 0 < α := lt_of_not_ge hnot
      have hneg : Gamble.StrictlyNegative ((0 : Gamble Ω) - (fun _ => α)) := by
        intro ω
        dsimp
        linarith
      exact avoid_sure_loss C ((0 : Gamble Ω) - (fun _ => α)) hneg hα
    have hle := le_csSup hbdd hmem
    linarith

/-- Positive scaling of a gamble scales its acceptable-price set. -/
theorem acceptablePrices_smul_eq
    {Ω : Type u}
    (C : CoherentDesirableSet Ω) (X : Gamble Ω) {r : ℝ} (hr : 0 < r) :
    acceptablePrices C (r • X) = r • acceptablePrices C X := by
  ext α
  constructor
  · intro hα
    refine ⟨α / r, ?_, ?_⟩
    · dsimp [acceptablePrices]
      have hscaled : (r⁻¹ : ℝ) • ((r • X) - (fun _ => α)) ∈ C.D :=
        C.D4 ((r • X) - (fun _ => α)) r⁻¹ hα (inv_pos.mpr hr)
      convert hscaled using 1
      funext ω
      dsimp
      field_simp [ne_of_gt hr]
    · simpa [smul_eq_mul] using (mul_div_cancel₀ α (ne_of_gt hr))
  · rintro ⟨β, hβ, hβα⟩
    dsimp [acceptablePrices] at hβ ⊢
    have hscaled : r • (X - (fun _ => β)) ∈ C.D :=
      C.D4 (X - (fun _ => β)) r hβ hr
    convert hscaled using 1
    funext ω
    dsimp at hβα ⊢
    rw [← hβα]
    ring

/-- The induced lower prevision is positively homogeneous on finite nonempty
outcome spaces. -/
theorem lowerPrevision_pos_homog
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C : CoherentDesirableSet Ω) (r : ℝ) (X : Gamble Ω) (hr : 0 ≤ r) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C (r • X) =
      r *
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          C X := by
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [lowerPrevision_zero]
  · dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision]
    change sSup (acceptablePrices C (r • X)) = r * sSup (acceptablePrices C X)
    rw [acceptablePrices_smul_eq C X hrpos, Real.sSup_smul_of_nonneg hr]
    simp [smul_eq_mul]

/-- Addition of acceptable prices is sound for the acceptable-price set of the
sum gamble. -/
theorem acceptablePrices_add_subset
    {Ω : Type u}
    (C : CoherentDesirableSet Ω) (X Y : Gamble Ω) :
    acceptablePrices C X + acceptablePrices C Y ⊆ acceptablePrices C (X + Y) := by
  intro γ hγ
  rw [Set.mem_add] at hγ
  rcases hγ with ⟨a, ha, b, hb, hsum⟩
  dsimp [acceptablePrices] at ha hb ⊢
  have hadd : (X - (fun _ => a)) + (Y - (fun _ => b)) ∈ C.D :=
    C.D3 (X - (fun _ => a)) (Y - (fun _ => b)) ha hb
  rw [← hsum]
  convert hadd using 1
  funext ω
  dsimp
  ring

/-- The induced lower prevision is superadditive on finite nonempty outcome
spaces. -/
theorem lowerPrevision_superadd
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C : CoherentDesirableSet Ω) (X Y : Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X +
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C Y ≤
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C (X + Y) := by
  dsimp [Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision]
  change sSup (acceptablePrices C X) + sSup (acceptablePrices C Y) ≤
    sSup (acceptablePrices C (X + Y))
  have hXne := acceptablePrices_nonempty C X
  have hYne := acceptablePrices_nonempty C Y
  have hXbdd := acceptablePrices_bddAbove C X
  have hYbdd := acceptablePrices_bddAbove C Y
  have hXYbdd := acceptablePrices_bddAbove C (X + Y)
  have hAddne : (acceptablePrices C X + acceptablePrices C Y).Nonempty := by
    rcases hXne with ⟨a, ha⟩
    rcases hYne with ⟨b, hb⟩
    exact ⟨a + b, Set.add_mem_add ha hb⟩
  rw [← csSup_add hXne hXbdd hYne hYbdd]
  apply csSup_le hAddne
  intro γ hγ
  exact le_csSup hXYbdd (acceptablePrices_add_subset C X Y hγ)

/-- Finite coherent desirable-gamble sets induce genuine lower previsions via
Walley's natural-extension `sSup` formula.  This is the finite reverse
direction to the lower-prevision-to-desirable-set construction; it intentionally
does not assert the full infinite-dimensional natural-extension theorem. -/
noncomputable def finiteLowerPrevision
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C : CoherentDesirableSet Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω where
  toFun :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      C
  lower_bound := by
    intro X c hc
    exact lowerPrevision_lower_bound C X c hc
  pos_homog := by
    intro r X hr
    exact lowerPrevision_pos_homog C r X hr
  superadd := by
    intro X Y
    exact lowerPrevision_superadd C X Y

@[simp] theorem finiteLowerPrevision_apply
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C : CoherentDesirableSet Ω) (X : Gamble Ω) :
    finiteLowerPrevision C X =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X :=
  rfl

end DesirableLowerPrevisionBridge

/-! ## Lower previsions as desirable-gamble sources -/

namespace LowerPrevisionDesirableBridge

open Mettapedia.ProbabilityTheory.ImpreciseProbability

/-- Regularity is the extra condition needed to turn the strict-positive
desirable-gamble axiom into a theorem for an arbitrary lower prevision.  It is
not a consequence of Walley's A1-A3 on infinite outcome spaces. -/
def Regular
    {Ω : Type u}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    Prop :=
  ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω,
    (∀ ω, X ω > 0) → P X > 0

/-- A regular lower prevision induces a coherent desirable-gamble set by taking
desirable gambles to be exactly those with strictly positive lower prevision. -/
noncomputable def coherentDesirableSet
    {Ω : Type u}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (hReg : Regular P) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω where
  D := {X | P X > 0}
  D1 := by
    intro h
    change P (0 : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) > 0 at h
    simp at h
  D2 := by
    intro X hX
    exact hReg X hX
  D3 := by
    intro X Y hX hY
    change P X > 0 at hX
    change P Y > 0 at hY
    change P (X + Y) > 0
    have hsup : P.toFun (X + Y) ≥ P.toFun X + P.toFun Y := P.superadd X Y
    linarith
  D4 := by
    intro X c hX hc
    change P X > 0 at hX
    change P (c • X) > 0
    rw [show P.toFun (c • X) = c * P.toFun X from P.pos_homog c X (le_of_lt hc)]
    exact mul_pos hc hX

@[simp] theorem coherentDesirableSet_mem
    {Ω : Type u}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (hReg : Regular P)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    X ∈ (coherentDesirableSet P hReg).D ↔ P X > 0 :=
  Iff.rfl

/-- On finite nonempty outcome spaces, every lower prevision is regular:
strict positivity has a positive finite minimum, and Walley's lower-bound axiom
pushes that minimum through the lower prevision. -/
theorem finite_regular
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    Regular P := by
  intro X hX
  let m := Finset.univ.inf' Finset.univ_nonempty X
  have hm_bound : ∀ ω, m ≤ X ω := fun ω => Finset.inf'_le X (Finset.mem_univ ω)
  obtain ⟨ω₀, _hω₀_mem, hω₀_min⟩ :=
    Finset.exists_min_image Finset.univ X Finset.univ_nonempty
  have hm_eq : m = X ω₀ := by
    apply le_antisymm
    · exact Finset.inf'_le X (Finset.mem_univ ω₀)
    · apply Finset.le_inf'
      intro ω _
      exact hω₀_min ω (Finset.mem_univ ω)
  have hm_pos : m > 0 := hm_eq ▸ hX ω₀
  have hPge := P.lower_bound X m hm_bound
  linarith

/-- The coherent desirable-gamble set induced by a lower prevision on a finite
nonempty outcome space. -/
noncomputable def finiteCoherentDesirableSet
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  coherentDesirableSet P (finite_regular P)

@[simp] theorem finiteCoherentDesirableSet_mem
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    X ∈ (finiteCoherentDesirableSet P).D ↔ P X > 0 :=
  Iff.rfl

/-- A nonempty finite credal set therefore also induces a coherent
desirable-gamble set, through its finite lower envelope lower prevision. -/
noncomputable def finiteCredalCoherentDesirableSet
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  finiteCoherentDesirableSet
    (FiniteCredalLowerPrevision.credalLowerPrevision K hK)

@[simp] theorem finiteCredalCoherentDesirableSet_mem
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    X ∈ (finiteCredalCoherentDesirableSet K hK).D ↔
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K X > 0 :=
  Iff.rfl

/-- Lower previsions assign a constant gamble its constant value.  This is the
cash-invariance part of Walley's A1-A3 package, derived rather than assumed. -/
theorem lowerPrevision_const
    {Ω : Type u}
    (P : LowerPrevision Ω) (c : ℝ) :
    P (Gamble.const c) = c := by
  apply le_antisymm
  · have hsup := P.superadd (Gamble.const c) (Gamble.const (-c))
    have hzero :
        (Gamble.const c : Gamble Ω) + Gamble.const (-c) = 0 := by
      funext ω
      change c + -c = 0
      ring
    rw [hzero, LowerPrevision.map_zero] at hsup
    have hneg :
        -c ≤ P (Gamble.const (-c) : Gamble Ω) :=
      P.lower_bound (Gamble.const (-c)) (-c) (by intro ω; exact le_rfl)
    linarith
  · exact P.lower_bound (Gamble.const c) c (by intro ω; exact le_rfl)

/-- Adding a constant gamble translates a lower prevision by that constant.
This is another cash-invariance consequence of A1-A3. -/
theorem lowerPrevision_add_const
    {Ω : Type u}
    (P : LowerPrevision Ω) (X : Gamble Ω) (c : ℝ) :
    P (X + Gamble.const c) = P X + c := by
  apply le_antisymm
  · have hsup := P.superadd (X + Gamble.const c) (Gamble.const (-c))
    have hback :
        (X + Gamble.const c) + Gamble.const (-c) = X := by
      funext ω
      change (X ω + c) + -c = X ω
      ring
    rw [hback] at hsup
    have hconst := lowerPrevision_const P (-c)
    linarith
  · have hsup := P.superadd X (Gamble.const c)
    have hconst := lowerPrevision_const P c
    linarith

/-- Subtracting a constant gamble translates a lower prevision by the negative
of that constant. -/
theorem lowerPrevision_sub_const
    {Ω : Type u}
    (P : LowerPrevision Ω) (X : Gamble Ω) (c : ℝ) :
    P (X - Gamble.const c) = P X - c := by
  have hsub : X - Gamble.const c = X + Gamble.const (-c) := by
    funext ω
    change X ω - c = X ω + -c
    ring
  rw [hsub, lowerPrevision_add_const P X (-c)]
  ring

/-- The acceptable prices induced by the desirable set `{X | P X > 0}` are
exactly the open ray of prices below `P X`. -/
theorem coherentDesirableSet_acceptablePrices_eq_Iio
    {Ω : Type u}
    (P : LowerPrevision Ω) (hReg : Regular P) (X : Gamble Ω) :
    DesirableLowerPrevisionBridge.acceptablePrices
      (coherentDesirableSet P hReg) X = Set.Iio (P X) := by
  ext α
  rw [Set.mem_Iio,
    show (α ∈ DesirableLowerPrevisionBridge.acceptablePrices (coherentDesirableSet P hReg) X)
        = (P (X - Gamble.const α) > 0) from rfl,
    lowerPrevision_sub_const]
  constructor <;> intro h <;> linarith

/-- Regular lower previsions round-trip through their induced desirable-gamble
set and Walley's acceptable-price supremum. -/
theorem coherentDesirableSet_lowerPrevision_roundtrip
    {Ω : Type u}
    (P : LowerPrevision Ω) (hReg : Regular P) (X : Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (coherentDesirableSet P hReg) X = P X := by
  change sSup
      (DesirableLowerPrevisionBridge.acceptablePrices
        (coherentDesirableSet P hReg) X) = P X
  rw [coherentDesirableSet_acceptablePrices_eq_Iio P hReg X, csSup_Iio]

/-- On finite nonempty outcome spaces, the lower-prevision → desirable-set →
finite-natural-extension round-trip recovers the original lower prevision
pointwise. -/
theorem finiteCoherentDesirableSet_lowerPrevision_roundtrip_apply
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (P : LowerPrevision Ω) (X : Gamble Ω) :
    DesirableLowerPrevisionBridge.finiteLowerPrevision
        (finiteCoherentDesirableSet P) X =
      P X := by
  change
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (finiteCoherentDesirableSet P) X = P X
  exact coherentDesirableSet_lowerPrevision_roundtrip P (finite_regular P) X

/-- On finite nonempty outcome spaces, the round-trip recovers the original
lower prevision as a structure, not merely as an informal correspondence. -/
theorem finiteCoherentDesirableSet_lowerPrevision_roundtrip
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (P : LowerPrevision Ω) :
    DesirableLowerPrevisionBridge.finiteLowerPrevision
        (finiteCoherentDesirableSet P) = P := by
  ext X
  exact finiteCoherentDesirableSet_lowerPrevision_roundtrip_apply P X

/-- The finite strict reconstruction of a coherent desirable-gamble set:
project to the finite lower prevision, then reconstruct the strict desirable
set `{X | P X > 0}`.  This is the canonical finite representative retained by
the lower-prevision projection. -/
noncomputable def finiteStrictRoundTrip
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  finiteCoherentDesirableSet
    (DesirableLowerPrevisionBridge.finiteLowerPrevision C)

@[simp] theorem finiteStrictRoundTrip_mem
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Gamble Ω) :
    X ∈ (finiteStrictRoundTrip C).D ↔
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X > 0 := by
  rfl

/-- Strict finite reconstruction preserves exactly the finite lower prevision
that it was built from. -/
theorem finiteStrictRoundTrip_finiteLowerPrevision_eq
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    DesirableLowerPrevisionBridge.finiteLowerPrevision
        (finiteStrictRoundTrip C) =
      DesirableLowerPrevisionBridge.finiteLowerPrevision C :=
  finiteCoherentDesirableSet_lowerPrevision_roundtrip
    (DesirableLowerPrevisionBridge.finiteLowerPrevision C)

/-- Strict finite reconstruction factors through the lower-prevision
projection: if two coherent desirable-gamble sets induce the same finite lower
prevision, the strict desirable sets reconstructed from that projection have
the same membership set. -/
theorem same_finiteLowerPrevision_same_strictRoundTrip_D
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (h :
      DesirableLowerPrevisionBridge.finiteLowerPrevision C =
        DesirableLowerPrevisionBridge.finiteLowerPrevision D) :
    (finiteCoherentDesirableSet
      (DesirableLowerPrevisionBridge.finiteLowerPrevision C)).D =
      (finiteCoherentDesirableSet
        (DesirableLowerPrevisionBridge.finiteLowerPrevision D)).D := by
  rw [h]

/-- Membership form of strict reconstruction factorization through the finite
lower-prevision projection. -/
theorem same_finiteLowerPrevision_same_strictRoundTrip_mem_iff
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (h :
      DesirableLowerPrevisionBridge.finiteLowerPrevision C =
        DesirableLowerPrevisionBridge.finiteLowerPrevision D)
    (X : Gamble Ω) :
    X ∈
        (finiteCoherentDesirableSet
          (DesirableLowerPrevisionBridge.finiteLowerPrevision C)).D ↔
      X ∈
        (finiteCoherentDesirableSet
          (DesirableLowerPrevisionBridge.finiteLowerPrevision D)).D := by
  rw [same_finiteLowerPrevision_same_strictRoundTrip_D C D h]

/-- Finite strict reconstruction is idempotent at the membership-set level:
once the lower-prevision projection has chosen its strict representative,
reconstructing again changes nothing. -/
theorem finiteStrictRoundTrip_idempotent_D
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    (finiteStrictRoundTrip (finiteStrictRoundTrip C)).D =
      (finiteStrictRoundTrip C).D :=
  same_finiteLowerPrevision_same_strictRoundTrip_D
    (finiteStrictRoundTrip C) C
    (finiteStrictRoundTrip_finiteLowerPrevision_eq C)

/-- Membership form of finite strict reconstruction idempotence. -/
theorem finiteStrictRoundTrip_idempotent_mem_iff
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Gamble Ω) :
    X ∈ (finiteStrictRoundTrip (finiteStrictRoundTrip C)).D ↔
      X ∈ (finiteStrictRoundTrip C).D := by
  rw [finiteStrictRoundTrip_idempotent_D C]

/-- Coherent desirable-gamble sets are equal once their membership sets are
equal; the remaining fields are proof witnesses of the same D1-D4 laws. -/
theorem coherentDesirableSet_ext_D
    {Ω : Type u}
    {C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω}
    (hD : C.D = D.D) :
    C = D := by
  cases C
  cases D
  simp at hD
  subst hD
  rfl

/-- A coherent desirable-gamble set is Archimedean/open when every desirable
gamble remains desirable after subtracting some strictly positive constant.

This is the extra condition needed for the strict lower-prevision view
`{X | P X > 0}` to recover the original desirable set, rather than only its
strict interior. -/
def ArchimedeanDesirableSet
    {Ω : Type u}
    (C :
  Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    Prop :=
  ∀ X : Gamble Ω, X ∈ C.D →
    ∃ ε : ℝ, 0 < ε ∧ X - Gamble.const ε ∈ C.D

/-- The strict desirable set induced by the finite natural extension is always
contained in the original coherent desirable set.  No openness hypothesis is
needed in this direction. -/
theorem finiteDesirableRoundTrip_subset_original
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    (finiteCoherentDesirableSet
      (DesirableLowerPrevisionBridge.finiteLowerPrevision C)).D ⊆ C.D := by
  intro X hX
  have hsup :
      0 <
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          C X := by
    simpa [DesirableLowerPrevisionBridge.finiteLowerPrevision_apply] using hX
  change 0 <
    sSup (DesirableLowerPrevisionBridge.acceptablePrices C X) at hsup
  rcases exists_lt_of_lt_csSup
      (DesirableLowerPrevisionBridge.acceptablePrices_nonempty C X)
      hsup with ⟨α, hα, hαpos⟩
  have hconst : ((fun _ : Ω => α) : Gamble Ω) ∈ C.D := by
    apply C.D2
    intro ω
    exact hαpos
  have hadd : (X - (fun _ : Ω => α)) + (fun _ : Ω => α) ∈ C.D :=
    C.D3 (X - (fun _ : Ω => α)) (fun _ : Ω => α) hα hconst
  have hsum : (X - (fun _ : Ω => α)) + (fun _ : Ω => α) = X := by
    funext ω
    change X ω - α + α = X ω
    ring
  simpa [hsum] using hadd

/-- Negative canary schema for the opposite round-trip: the strict
lower-prevision view cannot recover any gamble whose induced lower prevision is
nonpositive.  Thus a coherent desirable set with boundary desirable gambles is
not recovered by `{X | P X > 0}` without an openness/Archimedean hypothesis. -/
theorem nonpositive_lowerPrevision_not_recovered_by_strict_roundtrip
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Gamble Ω)
    (hBoundary :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0) :
    X ∉
      (finiteCoherentDesirableSet
        (DesirableLowerPrevisionBridge.finiteLowerPrevision C)).D := by
  intro hX
  replace hX : DesirableLowerPrevisionBridge.finiteLowerPrevision C X > 0 := hX
  have hpos :
      0 <
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          C X := by
    simpa [DesirableLowerPrevisionBridge.finiteLowerPrevision_apply] using hX
  linarith

/-- Under the Archimedean/open desirability condition, the original coherent
desirable set is contained in the strict desirable set induced by the finite
natural extension. -/
theorem original_subset_finiteDesirableRoundTrip_of_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : ArchimedeanDesirableSet C) :
    C.D ⊆
      (finiteCoherentDesirableSet
        (DesirableLowerPrevisionBridge.finiteLowerPrevision C)).D := by
  intro X hX
  rcases hArch X hX with ⟨ε, hεpos, hε⟩
  rw [finiteCoherentDesirableSet_mem]
  have hle :
      ε ≤
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          C X := by
    change ε ≤ sSup (DesirableLowerPrevisionBridge.acceptablePrices C X)
    apply le_csSup (DesirableLowerPrevisionBridge.acceptablePrices_bddAbove C X)
    change X - (fun _ => ε) ∈ C.D
    exact hε
  simpa [DesirableLowerPrevisionBridge.finiteLowerPrevision_apply] using
    (lt_of_lt_of_le hεpos hle)

/-- For Archimedean/open coherent desirable sets, the finite
desirable-set → lower-prevision → strict-desirable-set round-trip recovers
membership exactly. -/
theorem finiteDesirableRoundTrip_mem_iff_of_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : ArchimedeanDesirableSet C)
    (X : Gamble Ω) :
    X ∈
        (finiteCoherentDesirableSet
          (DesirableLowerPrevisionBridge.finiteLowerPrevision C)).D ↔
      X ∈ C.D :=
  ⟨fun hX => finiteDesirableRoundTrip_subset_original C hX,
    fun hX => original_subset_finiteDesirableRoundTrip_of_archimedean C hArch hX⟩

/-- For Archimedean/open coherent desirable sets, the finite round-trip
recovers the original desirable-gamble membership set. -/
theorem finiteDesirableRoundTrip_D_eq_of_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : ArchimedeanDesirableSet C) :
    (finiteCoherentDesirableSet
      (DesirableLowerPrevisionBridge.finiteLowerPrevision C)).D = C.D := by
  ext X
  exact finiteDesirableRoundTrip_mem_iff_of_archimedean C hArch X

/-- Operator-named version of the one-way finite strict reconstruction law:
the canonical strict representative is always contained in the original
coherent desirable set. -/
theorem finiteStrictRoundTrip_subset_original
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    (finiteStrictRoundTrip C).D ⊆ C.D :=
  finiteDesirableRoundTrip_subset_original C

/-- Operator-named boundary canary: a gamble whose induced lower prevision is
nonpositive is not recovered by finite strict reconstruction. -/
theorem finiteStrictRoundTrip_not_mem_of_nonpositive_lowerPrevision
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Gamble Ω)
    (hBoundary :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0) :
    X ∉ (finiteStrictRoundTrip C).D :=
  nonpositive_lowerPrevision_not_recovered_by_strict_roundtrip C X hBoundary

/-- Under the Archimedean/open condition, finite strict reconstruction contains
the original coherent desirable set. -/
theorem original_subset_finiteStrictRoundTrip_of_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : ArchimedeanDesirableSet C) :
    C.D ⊆ (finiteStrictRoundTrip C).D :=
  original_subset_finiteDesirableRoundTrip_of_archimedean C hArch

/-- Operator-named membership recovery law: Archimedean/open coherent desirable
sets are exactly the fixed points of finite strict reconstruction at the
membership level. -/
theorem finiteStrictRoundTrip_mem_iff_of_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : ArchimedeanDesirableSet C)
    (X : Gamble Ω) :
    X ∈ (finiteStrictRoundTrip C).D ↔ X ∈ C.D :=
  finiteDesirableRoundTrip_mem_iff_of_archimedean C hArch X

/-- Operator-named set recovery law for Archimedean/open coherent desirable
sets. -/
theorem finiteStrictRoundTrip_D_eq_of_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : ArchimedeanDesirableSet C) :
    (finiteStrictRoundTrip C).D = C.D :=
  finiteDesirableRoundTrip_D_eq_of_archimedean C hArch

/-- Full structure-level fixed-point law: on finite nonempty outcome spaces,
Archimedean/open coherent desirable-gamble sets are fixed by finite strict
reconstruction. -/
theorem finiteStrictRoundTrip_eq_of_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : ArchimedeanDesirableSet C) :
    finiteStrictRoundTrip C = C :=
  coherentDesirableSet_ext_D
    (finiteStrictRoundTrip_D_eq_of_archimedean C hArch)

/-- The strict desirable set induced by a finite lower prevision is always
Archimedean/open. -/
theorem finiteCoherentDesirableSet_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (P : LowerPrevision Ω) :
    ArchimedeanDesirableSet (finiteCoherentDesirableSet P) := by
  intro X hX
  replace hX : P X > 0 := hX
  refine ⟨P X / 2, by linarith, ?_⟩
  show P (X - Gamble.const (P X / 2)) > 0
  rw [lowerPrevision_sub_const]
  linarith

/-- The finite strict reconstruction always lands in the Archimedean/open
desirable-gamble sets. -/
theorem finiteStrictRoundTrip_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    ArchimedeanDesirableSet (finiteStrictRoundTrip C) :=
  finiteCoherentDesirableSet_archimedean
    (DesirableLowerPrevisionBridge.finiteLowerPrevision C)

/-- Exact fixed-point characterization: a finite coherent desirable-gamble set
is fixed by strict lower-prevision reconstruction iff it is Archimedean/open. -/
theorem finiteStrictRoundTrip_eq_iff_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    finiteStrictRoundTrip C = C ↔ ArchimedeanDesirableSet C := by
  constructor
  · intro h
    rw [← h]
    exact finiteStrictRoundTrip_archimedean C
  · intro h
    exact finiteStrictRoundTrip_eq_of_archimedean C h

/-- Desirable-set inclusion makes the induced finite lower prevision monotone:
more accepted gambles give weakly larger acceptable prices. -/
theorem finiteLowerPrevision_mono_of_desirable_subset
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hCD : C.D ⊆ D.D)
    (X : Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision C X ≤
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision D X := by
  change sSup (DesirableLowerPrevisionBridge.acceptablePrices C X) ≤
    sSup (DesirableLowerPrevisionBridge.acceptablePrices D X)
  apply csSup_le (DesirableLowerPrevisionBridge.acceptablePrices_nonempty C X)
  intro α hα
  exact le_csSup (DesirableLowerPrevisionBridge.acceptablePrices_bddAbove D X)
    (hCD hα)

/-- The finite strict reconstruction is monotone with respect to desirable-set
inclusion.  Together with subset and idempotence, this is the finite interior
operator law for the open/Archimedean representative retained by lower
prevision. -/
theorem finiteStrictRoundTrip_mono_D
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hCD : C.D ⊆ D.D) :
    (finiteStrictRoundTrip C).D ⊆ (finiteStrictRoundTrip D).D := by
  intro X hX
  replace hX : DesirableGambles.lowerPrevision C X > 0 := hX
  show DesirableGambles.lowerPrevision D X > 0
  have hle := finiteLowerPrevision_mono_of_desirable_subset C D hCD X
  linarith

/-- Universal property of finite strict reconstruction: it is the greatest
Archimedean/open coherent desirable-gamble subset retained below the original
coherent desirable set. -/
theorem finiteStrictRoundTrip_greatest_archimedean_subset_D
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hDArch : ArchimedeanDesirableSet D)
    (hDC : D.D ⊆ C.D) :
    D.D ⊆ (finiteStrictRoundTrip C).D := by
  intro X hX
  have hFX : X ∈ (finiteStrictRoundTrip D).D := by
    rw [finiteStrictRoundTrip_D_eq_of_archimedean D hDArch]
    exact hX
  exact finiteStrictRoundTrip_mono_D D C hDC hFX

/-- Adjunction-style form of the finite strict reconstruction universal property:
for an Archimedean/open desirable set `D`, being below the canonical strict
representative of `C` is equivalent to being below `C` itself. -/
theorem finiteStrictRoundTrip_archimedean_subset_iff
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hDArch : ArchimedeanDesirableSet D) :
    D.D ⊆ (finiteStrictRoundTrip C).D ↔ D.D ⊆ C.D := by
  constructor
  · intro hDC X hX
    exact finiteStrictRoundTrip_subset_original C (hDC hX)
  · intro hDC
    exact finiteStrictRoundTrip_greatest_archimedean_subset_D C D hDArch hDC

/-- The strict positive cone of gambles.

Unlike the closed positive cone below, this desirable set is Archimedean/open on
finite nonempty outcome spaces: every strictly positive gamble has a positive
finite minimum, so it can be shifted downward a little while remaining
desirable. -/
def strictlyPositiveDesirableSet
    (Ω : Type u) [Nonempty Ω] :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω where
  D := {X : Gamble Ω | ∀ ω, 0 < X ω}
  D1 := by
    intro hzero
    let ω : Ω := Classical.choice inferInstance
    have hω := hzero ω
    simp at hω
  D2 := by
    intro X hX
    exact hX
  D3 := by
    intro X Y hX hY ω
    exact add_pos (hX ω) (hY ω)
  D4 := by
    intro X c hX hc ω
    simpa using mul_pos hc (hX ω)

@[simp] theorem strictlyPositiveDesirableSet_mem_iff
    {Ω : Type u} [Nonempty Ω] (X : Gamble Ω) :
    X ∈ (strictlyPositiveDesirableSet Ω).D ↔ ∀ ω, 0 < X ω :=
  Iff.rfl

/-- On finite nonempty outcome spaces, the strict positive cone is
Archimedean/open. -/
theorem strictlyPositiveDesirableSet_archimedean
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] :
    ArchimedeanDesirableSet (strictlyPositiveDesirableSet Ω) := by
  intro X hX
  let m := Finset.univ.inf' Finset.univ_nonempty X
  obtain ⟨ω₀, _hω₀_mem, hω₀_min⟩ :=
    Finset.exists_min_image Finset.univ X Finset.univ_nonempty
  have hm_eq : m = X ω₀ := by
    apply le_antisymm
    · exact Finset.inf'_le X (Finset.mem_univ ω₀)
    · apply Finset.le_inf'
      intro ω _
      exact hω₀_min ω (Finset.mem_univ ω)
  have hm_pos : 0 < m := hm_eq ▸ hX ω₀
  refine ⟨m / 2, by linarith, ?_⟩
  intro ω
  have hm_le : m ≤ X ω := Finset.inf'_le X (Finset.mem_univ ω)
  change 0 < X ω - Gamble.const (m / 2) ω
  simp [Gamble.const]
  linarith

/-- Positive contrast to the boundary canary: for the strict positive cone,
the finite desirable-set → lower-prevision → strict-desirable-set round-trip
does recover the original desirable set. -/
theorem strictlyPositiveDesirableSet_roundtrip_D_eq
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] :
    (finiteCoherentDesirableSet
      (DesirableLowerPrevisionBridge.finiteLowerPrevision
        (strictlyPositiveDesirableSet Ω))).D =
      (strictlyPositiveDesirableSet Ω).D :=
  finiteDesirableRoundTrip_D_eq_of_archimedean
    (strictlyPositiveDesirableSet Ω)
    strictlyPositiveDesirableSet_archimedean

/-- Membership version of the strict-positive contrast: after the finite
round-trip, a gamble is recovered exactly when it is strictly positive. -/
theorem strictlyPositiveDesirableSet_roundtrip_mem_iff
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] (X : Gamble Ω) :
    X ∈
        (finiteCoherentDesirableSet
          (DesirableLowerPrevisionBridge.finiteLowerPrevision
            (strictlyPositiveDesirableSet Ω))).D ↔
      (∀ ω, 0 < X ω) := by
  rw [strictlyPositiveDesirableSet_roundtrip_D_eq]
  exact strictlyPositiveDesirableSet_mem_iff X

/-- The acceptable prices of a gamble in the strict positive cone are exactly
the open ray below its finite pointwise minimum. -/
theorem strictlyPositiveDesirableSet_acceptablePrices_eq_Iio
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] (X : Gamble Ω) :
    DesirableLowerPrevisionBridge.acceptablePrices
        (strictlyPositiveDesirableSet Ω) X =
      Set.Iio (DesirableLowerPrevisionBridge.finiteMinimum X) := by
  ext α
  dsimp [DesirableLowerPrevisionBridge.acceptablePrices]
  rw [Set.mem_Iio]
  constructor
  · intro hα
    rcases DesirableLowerPrevisionBridge.exists_apply_eq_finiteMinimum X with
      ⟨ω₀, hω₀⟩
    have hω := hα ω₀
    dsimp at hω
    rw [hω₀] at hω
    change α < DesirableLowerPrevisionBridge.finiteMinimum X
    linarith
  · intro hα ω
    change α < DesirableLowerPrevisionBridge.finiteMinimum X at hα
    have hmle := DesirableLowerPrevisionBridge.finiteMinimum_le_apply X ω
    dsimp
    linarith

/-- The lower prevision induced by the strict positive cone is the finite
pointwise minimum.  This is the vacuous lower expectation on a finite outcome
space. -/
theorem strictlyPositiveDesirableSet_lowerPrevision_eq_finiteMinimum
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] (X : Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (strictlyPositiveDesirableSet Ω) X =
        DesirableLowerPrevisionBridge.finiteMinimum X := by
  change sSup
    (DesirableLowerPrevisionBridge.acceptablePrices
      (strictlyPositiveDesirableSet Ω) X) =
        DesirableLowerPrevisionBridge.finiteMinimum X
  rw [strictlyPositiveDesirableSet_acceptablePrices_eq_Iio X, csSup_Iio]

/-- The closed positive cone of nonzero nonnegative gambles.

It is coherent as a D1-D4 desirable set, but it is not Archimedean/open: a
gamble that touches the boundary at zero cannot be shifted downward by any
strictly positive constant while staying nonnegative. -/
def nonnegativeNonzeroDesirableSet
    (Ω : Type u) [Nonempty Ω] :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω where
  D := {X : Gamble Ω | (∀ ω, 0 ≤ X ω) ∧ ∃ ω, 0 < X ω}
  D1 := by
    rintro ⟨_hNonneg, ⟨ω, hpos⟩⟩
    simp at hpos
  D2 := by
    intro X hX
    exact ⟨fun ω => le_of_lt (hX ω),
      let ω : Ω := Classical.choice inferInstance
      ⟨ω, hX ω⟩⟩
  D3 := by
    intro X Y hX hY
    rcases hX with ⟨hXnonneg, ⟨ω, hXpos⟩⟩
    rcases hY with ⟨hYnonneg, _hYpos⟩
    refine ⟨?_, ⟨ω, ?_⟩⟩
    · intro ω'
      exact add_nonneg (hXnonneg ω') (hYnonneg ω')
    · have hYω := hYnonneg ω
      dsimp
      linarith
  D4 := by
    intro X c hX hc
    rcases hX with ⟨hXnonneg, ⟨ω, hXpos⟩⟩
    refine ⟨?_, ⟨ω, ?_⟩⟩
    · intro ω'
      simpa using mul_nonneg (le_of_lt hc) (hXnonneg ω')
    · simpa using mul_pos hc hXpos

@[simp] theorem nonnegativeNonzeroDesirableSet_mem_iff
    {Ω : Type u} [Nonempty Ω] (X : Gamble Ω) :
    X ∈ (nonnegativeNonzeroDesirableSet Ω).D ↔
      (∀ ω, 0 ≤ X ω) ∧ ∃ ω, 0 < X ω :=
  Iff.rfl

/-- The closed positive cone induces the same finite lower prevision as the
strict positive cone: the finite pointwise minimum.  The lower-prevision
projection therefore forgets the boundary distinction between `X > 0` and
`X ≥ 0` with `X ≠ 0`. -/
theorem nonnegativeNonzeroDesirableSet_lowerPrevision_eq_finiteMinimum
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] (X : Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegativeNonzeroDesirableSet Ω) X =
        DesirableLowerPrevisionBridge.finiteMinimum X := by
  apply le_antisymm
  · change sSup
      (DesirableLowerPrevisionBridge.acceptablePrices
        (nonnegativeNonzeroDesirableSet Ω) X) ≤
          DesirableLowerPrevisionBridge.finiteMinimum X
    apply csSup_le
    · exact DesirableLowerPrevisionBridge.acceptablePrices_nonempty
        (nonnegativeNonzeroDesirableSet Ω) X
    · intro α hα
      dsimp [DesirableLowerPrevisionBridge.acceptablePrices] at hα
      rcases DesirableLowerPrevisionBridge.exists_apply_eq_finiteMinimum X with
        ⟨ω₀, hω₀⟩
      have hω := hα.1 ω₀
      dsimp at hω
      linarith
  · change DesirableLowerPrevisionBridge.finiteMinimum X ≤
      sSup
        (DesirableLowerPrevisionBridge.acceptablePrices
          (nonnegativeNonzeroDesirableSet Ω) X)
    apply le_of_forall_pos_le_add
    intro ε hε
    have hmem :
        DesirableLowerPrevisionBridge.finiteMinimum X - ε ∈
          DesirableLowerPrevisionBridge.acceptablePrices
            (nonnegativeNonzeroDesirableSet Ω) X := by
      dsimp [DesirableLowerPrevisionBridge.acceptablePrices]
      refine ⟨?_, ?_⟩
      · intro ω
        have hmle := DesirableLowerPrevisionBridge.finiteMinimum_le_apply X ω
        dsimp
        linarith
      · let ω : Ω := Classical.choice inferInstance
        refine ⟨ω, ?_⟩
        have hmle := DesirableLowerPrevisionBridge.finiteMinimum_le_apply X ω
        dsimp
        linarith
    have hle := le_csSup
      (DesirableLowerPrevisionBridge.acceptablePrices_bddAbove
        (nonnegativeNonzeroDesirableSet Ω) X) hmem
    linarith

/-- Exact mechanism of the strict/open boundary loss: the strict and closed
positive cones induce the same finite lower prevision, even though the closed
cone has extra boundary gambles that the strict reconstruction later drops. -/
theorem positiveCones_induce_same_lowerPrevision
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] (X : Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (strictlyPositiveDesirableSet Ω) X =
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegativeNonzeroDesirableSet Ω) X := by
  rw [strictlyPositiveDesirableSet_lowerPrevision_eq_finiteMinimum,
    nonnegativeNonzeroDesirableSet_lowerPrevision_eq_finiteMinimum]

/-- The strict/open and closed positive cones are identified by the finite
desirable-set → lower-prevision projection.  This is the projection-level form
of `positiveCones_induce_same_lowerPrevision`: lower previsions remember the
forced buying prices, not every boundary membership decision in the source
desirable-gamble set. -/
theorem positiveCones_induce_same_finiteLowerPrevision
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] :
    DesirableLowerPrevisionBridge.finiteLowerPrevision
        (strictlyPositiveDesirableSet Ω) =
      DesirableLowerPrevisionBridge.finiteLowerPrevision
        (nonnegativeNonzeroDesirableSet Ω) := by
  ext X
  exact positiveCones_induce_same_lowerPrevision X

/-- Exact canonicalization result: if the closed positive cone is projected to
a finite lower prevision and then reconstructed by the strict/open
lower-prevision-to-desirable-set rule, the recovered set is exactly the strict
positive cone.  This is the general finite version of the Bool boundary
canary. -/
theorem nonnegativeNonzeroDesirableSet_strictRoundTrip_D_eq_strictlyPositive
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] :
    (finiteCoherentDesirableSet
      (DesirableLowerPrevisionBridge.finiteLowerPrevision
        (nonnegativeNonzeroDesirableSet Ω))).D =
      (strictlyPositiveDesirableSet Ω).D := by
  rw [← positiveCones_induce_same_finiteLowerPrevision]
  exact strictlyPositiveDesirableSet_roundtrip_D_eq

/-- Membership form of the finite canonicalization result: the strict
round-trip of the closed positive cone recovers precisely the strictly positive
gambles. -/
theorem nonnegativeNonzeroDesirableSet_strictRoundTrip_mem_iff
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] (X : Gamble Ω) :
    X ∈
        (finiteCoherentDesirableSet
          (DesirableLowerPrevisionBridge.finiteLowerPrevision
            (nonnegativeNonzeroDesirableSet Ω))).D ↔
      (∀ ω, 0 < X ω) := by
  rw [nonnegativeNonzeroDesirableSet_strictRoundTrip_D_eq_strictlyPositive]
  exact strictlyPositiveDesirableSet_mem_iff X

/-- The finite Bool boundary gamble: zero at `false`, one at `true`. -/
def boolBoundaryGamble : Gamble Bool := fun b => if b then 1 else 0

@[simp] theorem boolBoundaryGamble_false :
    boolBoundaryGamble false = 0 := by
  simp [boolBoundaryGamble]

@[simp] theorem boolBoundaryGamble_true :
    boolBoundaryGamble true = 1 := by
  simp [boolBoundaryGamble]

/-- The Bool boundary gamble is desirable in the closed positive cone. -/
theorem boolBoundaryGamble_mem_nonnegativeNonzero :
    boolBoundaryGamble ∈ (nonnegativeNonzeroDesirableSet Bool).D := by
  rw [nonnegativeNonzeroDesirableSet_mem_iff]
  constructor
  · intro b
    cases b <;> norm_num [boolBoundaryGamble]
  · exact ⟨true, by norm_num [boolBoundaryGamble]⟩

/-- The Bool boundary gamble is not desirable in the strict positive cone,
because its `false` coordinate is exactly zero. -/
theorem boolBoundaryGamble_not_mem_strictlyPositive :
    boolBoundaryGamble ∉ (strictlyPositiveDesirableSet Bool).D := by
  intro hmem
  rw [strictlyPositiveDesirableSet_mem_iff] at hmem
  have hfalse := hmem false
  simp [boolBoundaryGamble] at hfalse

/-- The strict/open and closed positive cones are genuinely different on Bool. -/
theorem strictAndClosedPositiveCones_distinct_bool :
    (strictlyPositiveDesirableSet Bool).D ≠
      (nonnegativeNonzeroDesirableSet Bool).D := by
  intro hEq
  exact boolBoundaryGamble_not_mem_strictlyPositive
    (by
      rw [hEq]
      exact boolBoundaryGamble_mem_nonnegativeNonzero)

/-- Concrete projection non-injectivity: on Bool, two distinct coherent
desirable-gamble sets induce the same finite lower prevision. -/
theorem bool_positiveCones_projection_not_injective :
    (strictlyPositiveDesirableSet Bool).D ≠
        (nonnegativeNonzeroDesirableSet Bool).D ∧
      DesirableLowerPrevisionBridge.finiteLowerPrevision
          (strictlyPositiveDesirableSet Bool) =
        DesirableLowerPrevisionBridge.finiteLowerPrevision
          (nonnegativeNonzeroDesirableSet Bool) := by
  exact ⟨strictAndClosedPositiveCones_distinct_bool,
    positiveCones_induce_same_finiteLowerPrevision⟩

/-- The boundary gamble's acceptable-price supremum is exactly zero in the
closed positive cone.  Price zero itself is acceptable, but every positive price
makes the `false` coordinate negative. -/
theorem boolBoundaryGamble_lowerPrevision_eq_zero :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegativeNonzeroDesirableSet Bool) boolBoundaryGamble = 0 := by
  change sSup
    (DesirableLowerPrevisionBridge.acceptablePrices
      (nonnegativeNonzeroDesirableSet Bool) boolBoundaryGamble) = 0
  have hzero_mem :
      0 ∈
        DesirableLowerPrevisionBridge.acceptablePrices
          (nonnegativeNonzeroDesirableSet Bool) boolBoundaryGamble := by
    dsimp [DesirableLowerPrevisionBridge.acceptablePrices]
    refine ⟨?_, ?_⟩
    · intro b
      cases b <;> norm_num [boolBoundaryGamble]
    · exact ⟨true, by norm_num [boolBoundaryGamble]⟩
  have hupper :
      ∀ α ∈
        DesirableLowerPrevisionBridge.acceptablePrices
          (nonnegativeNonzeroDesirableSet Bool) boolBoundaryGamble,
        α ≤ 0 := by
    intro α hα
    dsimp [DesirableLowerPrevisionBridge.acceptablePrices] at hα
    have hfalse := hα.1 false
    dsimp [boolBoundaryGamble] at hfalse
    linarith
  have hbdd :
      BddAbove
        (DesirableLowerPrevisionBridge.acceptablePrices
          (nonnegativeNonzeroDesirableSet Bool) boolBoundaryGamble) :=
    ⟨0, hupper⟩
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, hzero_mem⟩
    · exact hupper
  · exact le_csSup hbdd hzero_mem

/-- Concrete boundary canary: the Bool boundary gamble is genuinely desirable
in the closed positive cone, has induced lower prevision exactly zero, and is
therefore dropped by the strict lower-prevision-to-desirable-set round-trip. -/
theorem concreteBool_boundary_desirable_not_recovered_by_strict_roundtrip :
    boolBoundaryGamble ∈ (nonnegativeNonzeroDesirableSet Bool).D ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (nonnegativeNonzeroDesirableSet Bool) boolBoundaryGamble = 0 ∧
      boolBoundaryGamble ∉
        (finiteCoherentDesirableSet
          (DesirableLowerPrevisionBridge.finiteLowerPrevision
            (nonnegativeNonzeroDesirableSet Bool))).D := by
  refine ⟨boolBoundaryGamble_mem_nonnegativeNonzero,
    boolBoundaryGamble_lowerPrevision_eq_zero, ?_⟩
  exact nonpositive_lowerPrevision_not_recovered_by_strict_roundtrip
    (nonnegativeNonzeroDesirableSet Bool) boolBoundaryGamble
    (by rw [boolBoundaryGamble_lowerPrevision_eq_zero])

/-- The closed positive cone is not Archimedean/open. -/
theorem nonnegativeNonzeroBool_not_archimedean :
    ¬ ArchimedeanDesirableSet (nonnegativeNonzeroDesirableSet Bool) := by
  intro hArch
  rcases hArch boolBoundaryGamble boolBoundaryGamble_mem_nonnegativeNonzero with
    ⟨ε, hεpos, hεmem⟩
  have hfalse := hεmem.1 false
  change 0 ≤ boolBoundaryGamble false - Gamble.const ε false at hfalse
  have hfalse' : 0 ≤ -ε := by
    simpa [boolBoundaryGamble] using hfalse
  linarith

/-- Concrete set-level canary: without Archimedean openness, the finite
desirable-set → lower-prevision → strict-desirable-set round-trip need not
recover the original desirable-gamble set. -/
theorem concreteBool_boundary_roundtrip_set_ne_original :
    (finiteCoherentDesirableSet
      (DesirableLowerPrevisionBridge.finiteLowerPrevision
        (nonnegativeNonzeroDesirableSet Bool))).D ≠
      (nonnegativeNonzeroDesirableSet Bool).D := by
  intro hEq
  have hRecovered :
      boolBoundaryGamble ∈
        (finiteCoherentDesirableSet
          (DesirableLowerPrevisionBridge.finiteLowerPrevision
            (nonnegativeNonzeroDesirableSet Bool))).D := by
    rw [hEq]
    exact boolBoundaryGamble_mem_nonnegativeNonzero
  exact
    (concreteBool_boundary_desirable_not_recovered_by_strict_roundtrip).2.2
      hRecovered

end LowerPrevisionDesirableBridge

/-! ## Credal projection tower: envelope plus chosen evidence coordinate -/

/-- A finite credal projection tower separates the imprecise-probability object
from the evidence-weight coordinate used as the displayed credibility.

The credal set and gamble force lower/upper endpoints.  The coordinate and
nonnegative evidence weight select the credibility display.  This is the
smallest typed object that makes the tower explicit:

`credal set + query` → forced envelope, and
`coordinate + weight` → selected confidence. -/
structure CredalProjectionTower (Ω : Type u) [Fintype Ω] where
  credal :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω
  credal_nonempty : credal.Nonempty
  gamble : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω
  gamble_in_unit : ∀ ω, gamble ω ∈ Set.Icc 0 1
  coordinate : EvidenceWeightCoordinate
  coordinate_unit : UnitIcoOnNonneg coordinate
  weight : ℝ
  weight_nonneg : 0 ≤ weight

namespace CredalProjectionTower

open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-- The selected credibility display is the chosen coordinate applied to the
evidence weight. -/
noncomputable def credibilityDisplay {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) : ℝ :=
  t.coordinate.encode t.weight

/-- The same selected display as a typed confidence value retaining coordinate
provenance. -/
noncomputable def typedConfidence {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) : TypedConfidence t.coordinate :=
  TypedConfidence.ofWeight t.coordinate t.weight

@[simp] theorem typedConfidence_display {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    t.typedConfidence.display = t.credibilityDisplay :=
  rfl

/-- The selected typed confidence decodes back to the tower's evidence weight. -/
@[simp] theorem typedConfidence_weight {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    t.typedConfidence.weight = t.weight :=
  TypedConfidence.weight_ofWeight t.coordinate t.weight_nonneg

/-- The coordinate admissibility hypothesis makes the selected credibility a
valid raw ITV credibility coordinate. -/
theorem credibilityDisplay_in_unit {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    t.credibilityDisplay ∈ Set.Icc 0 1 := by
  have h := t.coordinate_unit t.weight_nonneg
  exact ⟨h.1, le_of_lt h.2⟩

/-- Forget the tower to the finite credal-envelope source expected by the
typed ITV semantics. -/
noncomputable def toEnvelopeSource {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) : CredalEnvelopeITVSource Ω where
  credal := t.credal
  gamble := t.gamble
  credal_nonempty := t.credal_nonempty
  gamble_in_unit := t.gamble_in_unit
  credibility := t.credibilityDisplay
  credibility_in_unit := t.credibilityDisplay_in_unit

/-- Project the tower to a typed ITV. -/
noncomputable def toTypedITV {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    TypedITV (credalEnvelopeITVSemantics Ω) :=
  TypedITV.fromCredalEnvelope t.toEnvelopeSource

@[simp] theorem lower_toTypedITV {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    t.toTypedITV.lower =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        t.credal t.gamble := by
  simp [toTypedITV, toEnvelopeSource]

@[simp] theorem upper_toTypedITV {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    t.toTypedITV.upper =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        t.credal t.gamble := by
  simp [toTypedITV, toEnvelopeSource]

@[simp] theorem credibility_toTypedITV {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    t.toTypedITV.credibility = t.credibilityDisplay := by
  simp [toTypedITV, toEnvelopeSource]

/-- The tower's midpoint point-estimate view.  Lower/upper are forced by the
credal envelope; this is the current midpoint projection of that envelope. -/
noncomputable def midpointDisplay {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) : ℝ :=
  t.toTypedITV.midpoint

/-- The midpoint view of a credal projection tower is exactly the average of
the forced lower/upper envelope. -/
@[simp] theorem midpointDisplay_eq_credal_average {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    t.midpointDisplay =
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          t.credal t.gamble +
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          t.credal t.gamble) / 2 := by
  simp [midpointDisplay, TypedITV.midpoint, TypedITV.value, toTypedITV,
    toEnvelopeSource, TypedITV.fromCredalEnvelope, credalEnvelopeITVSemantics,
    credalEnvelopeITV, ITV.strength]

/-- The forced lower envelope is below the tower's midpoint view. -/
theorem lower_le_midpointDisplay {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    t.toTypedITV.lower ≤ t.midpointDisplay := by
  simpa [midpointDisplay] using
    (TypedITV.lower_le_midpoint (Sem := credalEnvelopeITVSemantics Ω) t.toTypedITV)

/-- The tower's midpoint view is below the forced upper envelope. -/
theorem midpointDisplay_le_upper {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) :
    t.midpointDisplay ≤ t.toTypedITV.upper := by
  simpa [midpointDisplay] using
    (TypedITV.midpoint_le_upper (Sem := credalEnvelopeITVSemantics Ω) t.toTypedITV)

/-- The bridge law that identifies evidence credibility with the complement of
credal imprecision.  It is deliberately an explicit hypothesis, not a generic
property of credal envelopes. -/
def WidthComplementBridge {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) : Prop :=
  t.toTypedITV.width + t.toTypedITV.credibility = 1

/-- Once the width-complement bridge is assumed, the selected display is forced
to be the complement of the envelope width. -/
theorem widthComplementBridge_forces_display {Ω : Type u} [Fintype Ω]
    (t : CredalProjectionTower Ω) (h : t.WidthComplementBridge) :
    t.credibilityDisplay = 1 - t.toTypedITV.width := by
  have hc : t.toTypedITV.credibility = t.credibilityDisplay := by
    simp
  have hsum : t.toTypedITV.width + t.toTypedITV.credibility = 1 := by
    simpa [WidthComplementBridge] using h
  calc
    t.credibilityDisplay = t.toTypedITV.credibility := hc.symm
    _ = 1 - t.toTypedITV.width := by linarith

/-- Even fixing the credal envelope and evidence weight does not determine the
displayed credibility unless the coordinate is fixed.  PLN odds and the
reserve-half coordinate both decode the same weight `1`, but display different
credibilities for the same lower/upper envelope. -/
theorem same_weight_can_display_different_credibility
    {Ω : Type u} [Fintype Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    let x : CredalProjectionTower Ω :=
      { credal := K
        credal_nonempty := hK
        gamble := f
        gamble_in_unit := hf
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    let y : CredalProjectionTower Ω :=
      { credal := K
        credal_nonempty := hK
        gamble := f
        gamble_in_unit := hf
        coordinate := reserveHalfCoordinate 1 (by norm_num)
        coordinate_unit := reserveHalfCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    x.toTypedITV.lower = y.toTypedITV.lower ∧
      x.toTypedITV.upper = y.toTypedITV.upper ∧
      x.toTypedITV.credibility ≠ y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight := by
  dsimp [toTypedITV, toEnvelopeSource, credibilityDisplay, typedConfidence,
    TypedITV.lower, TypedITV.upper, TypedITV.credibility, TypedITV.value,
    TypedITV.fromCredalEnvelope, credalEnvelopeITVSemantics, credalEnvelopeITV,
    TypedConfidence.weight, TypedConfidence.ofWeight, plnOddsCoordinate,
    reserveHalfCoordinate]
  norm_num

/-- Fixing the coordinate and evidence weight fixes the displayed confidence,
independently of which credal envelope is being queried. -/
theorem same_coordinate_weight_forces_same_confidence
    {Ω : Type u} [Fintype Ω]
    (K₁ K₂ :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1)
    (χ : EvidenceWeightCoordinate) (hχ : UnitIcoOnNonneg χ)
    (w : ℝ) (hw : 0 ≤ w) :
    let x : CredalProjectionTower Ω :=
      { credal := K₁
        credal_nonempty := hK₁
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    let y : CredalProjectionTower Ω :=
      { credal := K₂
        credal_nonempty := hK₂
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight := by
  dsimp [toTypedITV, toEnvelopeSource, credibilityDisplay, typedConfidence,
    TypedITV.credibility, TypedITV.value, TypedITV.fromCredalEnvelope,
    credalEnvelopeITVSemantics, credalEnvelopeITV, TypedConfidence.weight,
    TypedConfidence.ofWeight]
  exact ⟨rfl, by simp [χ.decode_encode_of_nonneg hw]⟩

/-- Dually, even with the same coordinate and evidence weight, changing the
retained credal source can change the lower envelope while leaving displayed
confidence and decoded evidence weight unchanged. -/
theorem same_confidence_can_have_different_credal_envelope
    {Ω : Type u} [Fintype Ω]
    (K₁ K₂ :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1)
    (χ : EvidenceWeightCoordinate) (hχ : UnitIcoOnNonneg χ)
    (w : ℝ) (hw : 0 ≤ w)
    (hLower :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K₁ f ≠
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K₂ f) :
    let x : CredalProjectionTower Ω :=
      { credal := K₁
        credal_nonempty := hK₁
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    let y : CredalProjectionTower Ω :=
      { credal := K₂
        credal_nonempty := hK₂
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight ∧
        x.toTypedITV.lower ≠ y.toTypedITV.lower := by
  dsimp [toTypedITV, toEnvelopeSource, credibilityDisplay, typedConfidence,
    TypedITV.lower, TypedITV.credibility, TypedITV.value,
    TypedITV.fromCredalEnvelope, credalEnvelopeITVSemantics, credalEnvelopeITV,
    TypedConfidence.weight, TypedConfidence.ofWeight]
  exact ⟨rfl, by simp [χ.decode_encode_of_nonneg hw], hLower⟩

/-- The Bool distribution assigning all mass to `false`. -/
def boolFalseProbDist : ProbDist Bool where
  prob b := if b then 0 else 1
  non_neg := by intro b; cases b <;> norm_num
  sum_one := by simp

/-- The Bool distribution assigning all mass to `true`. -/
def boolTrueProbDist : ProbDist Bool where
  prob b := if b then 1 else 0
  non_neg := by intro b; cases b <;> norm_num
  sum_one := by simp

/-- The unit gamble that asks whether the Bool state is `true`. -/
def boolTruthGamble : Gamble Bool := fun b => if b then 1 else 0

@[simp] theorem boolTruthGamble_in_unit :
    ∀ b, boolTruthGamble b ∈ Set.Icc (0 : ℝ) 1 := by
  intro b
  cases b <;> norm_num [boolTruthGamble]

@[simp] theorem boolFalse_lowerProb_eq_zero :
    lowerProb (Set.singleton boolFalseProbDist) boolTruthGamble = 0 := by
  rw [lowerProb_singleton_eq_expectedValue]
  simp [expectedValue, boolFalseProbDist, boolTruthGamble]

@[simp] theorem boolTrue_lowerProb_eq_one :
    lowerProb (Set.singleton boolTrueProbDist) boolTruthGamble = 1 := by
  rw [lowerProb_singleton_eq_expectedValue]
  simp [expectedValue, boolTrueProbDist, boolTruthGamble]

/-- Concrete lower-envelope separation used by the finite Bool canary. -/
theorem bool_singleton_lowerProb_different :
    lowerProb (Set.singleton boolFalseProbDist) boolTruthGamble ≠
      lowerProb (Set.singleton boolTrueProbDist) boolTruthGamble := by
  rw [boolFalse_lowerProb_eq_zero, boolTrue_lowerProb_eq_one]
  norm_num

/-- Concrete finite canary: two singleton Bool credal sets give the same
displayed confidence under the same coordinate and evidence weight, but force
different lower envelopes for the truth-indicator query. -/
theorem concreteBool_same_confidence_different_credal_envelope :
    let x : CredalProjectionTower Bool :=
      { credal := Set.singleton boolFalseProbDist
        credal_nonempty := ⟨boolFalseProbDist, rfl⟩
        gamble := boolTruthGamble
        gamble_in_unit := boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    let y : CredalProjectionTower Bool :=
      { credal := Set.singleton boolTrueProbDist
        credal_nonempty := ⟨boolTrueProbDist, rfl⟩
        gamble := boolTruthGamble
        gamble_in_unit := boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight ∧
      x.toTypedITV.lower = 0 ∧
      y.toTypedITV.lower = 1 ∧
      x.toTypedITV.lower ≠ y.toTypedITV.lower := by
  dsimp [toTypedITV, toEnvelopeSource, credibilityDisplay, typedConfidence,
    TypedITV.lower, TypedITV.credibility, TypedITV.value,
    TypedITV.fromCredalEnvelope, credalEnvelopeITVSemantics, credalEnvelopeITV,
    TypedConfidence.weight, TypedConfidence.ofWeight]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [plnOddsCoordinate]
  · exact boolFalse_lowerProb_eq_zero
  · exact boolTrue_lowerProb_eq_one
  · rw [boolFalse_lowerProb_eq_zero, boolTrue_lowerProb_eq_one]
    norm_num

end CredalProjectionTower

/-- A singleton family of Knuth-Skilling `Θ` completions has no interval spread:
the induced interval semantics is just the point semantics duplicated as lower
and upper. -/
theorem thetaSingleton_collapses_to_point
    {α β : Type*} [CompleteLattice β] (Θ₀ : α → β) :
    Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.intervalOfFamily
        (Set.singleton Θ₀) = ⟨Θ₀, Θ₀⟩ :=
  Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.intervalOfFamily_singleton Θ₀

/-- The existing Walley ITV bounds are the lower/upper true-event expectations
of the binary IDM credal set.  The ITV's `credibility` field remains a separate
evidence-concentration coordinate. -/
theorem walleyCredalEnvelope_matches_ITV_bounds
    (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (Mettapedia.Logic.WalleyBinaryIDM.credalSetOfEvidence e s hs)
        Mettapedia.Logic.WalleyBinaryIDM.trueGamble =
          (ITV.fromWalleyIDMPredictive e s hs).lower ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (Mettapedia.Logic.WalleyBinaryIDM.credalSetOfEvidence e s hs)
        Mettapedia.Logic.WalleyBinaryIDM.trueGamble =
          (ITV.fromWalleyIDMPredictive e s hs).upper :=
  Mettapedia.Logic.WalleyBinaryIDM.credal_envelope_matches_Walley_ITV_bounds e s hs

/-- Multinomial IDM category envelopes have the same width law as the binary
slice whenever there is another category to receive all prior mass.  This is the
honest categorical lift of the binary Walley bridge; the degenerate one-category
case is intentionally excluded. -/
theorem walleyMultinomial_category_width
    {k : ℕ} (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (s : ℝ) (hs : 0 < s) (i j : Fin k) (hji : j ≠ i) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e s hs)
        (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) -
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e s hs)
        (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) =
      s / ((e.total : ℝ) + s) :=
  Mettapedia.Logic.WalleyMultinomialIDM.category_width_eq_idmWidth_of_other
    e s hs i j hji

/-- The multinomial credal-set category envelope agrees with the existing
`EvidenceDirichlet` IDM lower/upper/width formulas.  The lower endpoint and
width need a distinct category to receive the unknown prior mass. -/
theorem walleyMultinomial_category_envelope_matches_EvidenceDirichlet
    {k : ℕ} (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (i j : Fin k) (hji : j ≠ i) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
        (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) =
          Mettapedia.Logic.EvidenceDirichlet.idmLower ctx e i ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
        (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) =
          Mettapedia.Logic.EvidenceDirichlet.idmUpper ctx e i ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
        (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) -
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) =
            Mettapedia.Logic.EvidenceDirichlet.idmWidth ctx e :=
  ⟨Mettapedia.Logic.WalleyMultinomialIDM.lowerProb_categoryGamble_eq_idmLower_of_other
      ctx e i j hji,
    Mettapedia.Logic.WalleyMultinomialIDM.upperProb_categoryGamble_eq_idmUpper
      ctx e i,
    Mettapedia.Logic.WalleyMultinomialIDM.category_width_eq_EvidenceDirichlet_idmWidth_of_other
      ctx e i j hji⟩

/-- In Walley's lower-prevision layer, zero imprecision for every gamble is
exactly precision.  This connects the ITV-width story to the more foundational
credal/lower-prevision object: intervals collapse only when the lower and
upper previsions agree everywhere. -/
theorem lowerPrevision_zero_imprecision_iff_precise
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    (∀ X, Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision P X = 0) ↔
      P.isPrecise :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision_zero_iff_precise P

/-! ## Knuth-Skilling precision layer -/

/-- A faithful point-valued representation into `ℝ` cannot exist when the
underlying Knuth-Skilling plausibility order has an incomparable pair.

This is the order-theoretic reason an interval/credal projection is sometimes
forced: a crisp scalar view would have to collapse a genuinely partial order
into a total one. -/
theorem ks_incomparable_forces_no_faithful_point_representation
    {α : Type*}
    [KnuthSkilling.TotalityImprecision.PartialKnuthSkillingAlgebra α]
    (x y : α)
    (hxy :
      KnuthSkilling.TotalityImprecision.PartialKnuthSkillingAlgebra.Incomparable
        x y) :
    ¬ ∃ (Θ : α → ℝ), ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b :=
  KnuthSkilling.TotalityImprecision.no_pointRepresentation_with_incomparables
    x y hxy

end Mettapedia.Logic.PLNTruthTower
