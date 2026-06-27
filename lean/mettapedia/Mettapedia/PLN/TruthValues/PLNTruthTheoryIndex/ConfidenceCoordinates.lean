import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.DefinableCuts

namespace Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex

open Mettapedia.PLN.WorldModel

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNInformationGeometry
open Mettapedia.PLN.TruthValues.PLNAmplitudePhase
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.Algebra.TwoDimClassification
open scoped ENNReal

universe u v


/-! ## Reconstructive confidence coordinates -/

/-- If a strength/confidence decoding reconstructs all positive finite binary
counts, its confidence coordinate must have a left inverse on positive total
weights. -/
theorem reconstructive_confidence_coordinates_need_left_inverse
    (encode decode : ℝ → ℝ)
    (h :
      ∀ {nPlus nMinus : ℝ},
        0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
          (let n := nPlus + nMinus
           let stv : ℝ × ℝ := (nPlus / n, encode n)
           let m := decode stv.2
           (stv.1 * m, (1 - stv.1) * m)) = (nPlus, nMinus))
    {w : ℝ} (hw : 0 < w) :
    decode (encode w) = w :=
  decode_encode_of_count_reconstruction encode decode h hw

/-- Exact characterization: count reconstruction is equivalent to the
confidence decoder being a left inverse of the encoder on positive evidence
weights. -/
theorem reconstructive_confidence_coordinates_iff_left_inverse
    (encode decode : ℝ → ℝ) :
    CountReconstruction encode decode ↔ LeftInverseOnPositive encode decode :=
  countReconstruction_iff_leftInverseOnPositive encode decode

/-- Conversely, any evidence-weight coordinate with a left inverse on
nonnegative weights is sufficient to reconstruct positive finite binary counts
from strength plus displayed confidence.  This is the exact freedom left by the
two-count problem: the coordinate must be invertible on total evidence, but it
need not be the PLN/NARS odds formula. -/
theorem evidence_weight_coordinate_suffices_for_binary_count_reconstruction
    (χ : EvidenceWeightCoordinate) {nPlus nMinus : ℝ}
    (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hTotal : nPlus + nMinus ≠ 0) :
    χ.decodeCounts (χ.encodeCounts nPlus nMinus) = (nPlus, nMinus) :=
  decode_encode_counts χ hPlus hMinus hTotal

/-- The PLN/NARS odds coordinate reconstructs counts because it has the same
left-inverse property as any other valid evidence-weight coordinate. -/
theorem pln_odds_coordinate_reconstructs_binary_counts
    (k : ℝ) (hk : 0 < k) {nPlus nMinus : ℝ}
    (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hTotal : nPlus + nMinus ≠ 0) :
    (plnOddsCoordinate k hk).decodeCounts
        ((plnOddsCoordinate k hk).encodeCounts nPlus nMinus) =
      (nPlus, nMinus) :=
  plnOddsCoordinate_decode_encode_counts k hk hPlus hMinus hTotal

/-- A non-PLN coordinate can still be reconstructive, so reconstruction alone
does not force the PLN/NARS confidence formula. -/
theorem reserve_half_coordinate_reconstructs_binary_counts
    (k : ℝ) (hk : 0 < k) {nPlus nMinus : ℝ}
    (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hTotal : nPlus + nMinus ≠ 0) :
    (reserveHalfCoordinate k hk).decodeCounts
        ((reserveHalfCoordinate k hk).encodeCounts nPlus nMinus) =
      (nPlus, nMinus) :=
  reserveHalfCoordinate_decode_encode_counts k hk hPlus hMinus hTotal

/-- Raw display equality is not a compatibility proof; provenance matters. -/
theorem same_confidence_display_can_decode_to_different_weights :
    let χp := plnOddsCoordinate 1 (by norm_num)
    let χr := reserveHalfCoordinate 1 (by norm_num)
    let cp : TypedConfidence χp := ⟨(1 / 3 : ℝ)⟩
    let cr : TypedConfidence χr := ⟨(1 / 3 : ℝ)⟩
    cp.display = cr.display ∧ cp.weight ≠ cr.weight :=
  raw_display_equality_does_not_determine_weight

/-- Concrete canary for the historical raw-min bug: the buggy confidence
formula strictly underestimates the weight-space formula on unit evidence. -/
theorem buggy_confidence_formula_underestimates_unit_weight :
    combineConfidenceBuggy ⟨0, 1⟩ ⟨0, 1⟩ 1 <
      combineConfidenceCorrect ⟨0, 1⟩ ⟨0, 1⟩ 1 :=
  combineConfidenceBuggy_underestimates_unit_weight

/-! ## PeTTa truth-function confidence audit -/

/-- The PeTTa induction mirror uses the intended weight-space minimum for
confidence. -/
theorem petta_induction_confidence_is_weight_min
    (a b c ba bc : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
        (min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w ba.c)
          (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w bc.c)) :=
  Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction_c_eq_weight_min
    a b c ba bc

/-- The PeTTa abduction mirror uses the intended weight-space minimum for
confidence. -/
theorem petta_abduction_confidence_is_weight_min
    (a b c ab cb : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c =
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
        (min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w ab.c)
          (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w cb.c)) :=
  Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction_c_eq_weight_min
    a b c ab cb

/-- Weight-space minimum collapses to raw minimum only after PeTTa's confidence
cap is made explicit. -/
theorem petta_weight_min_collapses_to_min_capped_confidence (c₁ c₂ : ℝ) :
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
        (min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w c₁)
          (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w c₂)) =
      min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf c₁)
        (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf c₂) :=
  Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c_min_c2w c₁ c₂

/-- PeTTa revision confidence is weight addition transported back through
`w2c`, with the mirror's final cap retained. -/
theorem petta_revision_confidence_is_weight_addition
    (t₁ t₂ : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthRevision t₁ t₂).c =
      min 1 (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
        (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w t₁.c +
          Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w t₂.c)) := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthRevision]

/-- PeTTa negation preserves confidence exactly. -/
theorem petta_negation_preserves_confidence
    (t : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthNegation t).c = t.c := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthNegation]

/-- PeTTa modus ponens multiplies premise confidences; this is a different
rule shape from the induction/abduction weight-space minimum. -/
theorem petta_modus_ponens_confidence_is_product
    (p pq : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c =
      p.c * pq.c := by
  simp [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens]

/-- Concrete canary: on two half-confident premises, PeTTa modus ponens'
product rule is strictly below raw minimum. -/
theorem petta_modus_ponens_product_below_min_canary :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens
        ⟨0, 0.5⟩ ⟨0, 0.5⟩).c <
      min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf 0.5)
        (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf 0.5) := by
  norm_num [Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf,
    Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.MAX_CONF]

/-! ## Generic ITV freedom -/

/-- Generic ITV width does not determine the credibility coordinate. -/
theorem generic_itv_width_does_not_force_credibility :
    ∃ itv₀ itv₁ : ITV,
      itv₀.width = itv₁.width ∧ itv₀.credibility ≠ itv₁.credibility :=
  genericITV_width_does_not_determine_credibility

/-- Generic ITV credibility does not determine interval width. -/
theorem generic_itv_credibility_does_not_force_width :
    ∃ itv₀ itv₁ : ITV,
      itv₀.credibility = itv₁.credibility ∧ itv₀.width ≠ itv₁.width :=
  genericITV_credibility_does_not_determine_width

/-- A generic interval does not force a unique point projection. -/
theorem generic_itv_does_not_force_point_projection :
    ∃ itv : ITV,
      Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .lower itv ≠
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .midpoint itv ∧
        Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .midpoint itv ≠
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .upper itv ∧
          Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .lower itv ≠
            Mettapedia.PLN.TruthValues.PLNForcedQueries.ITVSelector.eval .upper itv :=
  genericITV_point_projection_not_forced

/-! ## Strength projection views -/

/-- For any typed ITV, the current midpoint strength view lies above the lower
endpoint. -/
theorem typed_itv_lower_le_midpoint
    {Sem : Mettapedia.PLN.TruthValues.PLNTruthTower.ITVSemantics}
    (x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV Sem) :
    x.lower ≤ x.midpoint :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.lower_le_midpoint x

/-- For any typed ITV, the current midpoint strength view lies below the upper
endpoint. -/
theorem typed_itv_midpoint_le_upper
    {Sem : Mettapedia.PLN.TruthValues.PLNTruthTower.ITVSemantics}
    (x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV Sem) :
    x.midpoint ≤ x.upper :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.midpoint_le_upper x

/-- For any typed ITV, the current midpoint strength view is unit-bounded. -/
theorem typed_itv_midpoint_in_unit
    {Sem : Mettapedia.PLN.TruthValues.PLNTruthTower.ITVSemantics}
    (x : Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV Sem) :
    x.midpoint ∈ Set.Icc (0 : ℝ) 1 :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV.midpoint_in_unit x

/-- In the credal projection tower, midpoint strength is exactly the average of
the forced lower/upper credal envelope. -/
theorem credal_projection_tower_midpoint_is_envelope_average
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω) :
    t.midpointDisplay =
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          t.credal t.gamble +
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          t.credal t.gamble) / 2 :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.midpointDisplay_eq_credal_average t

/-- In the credal projection tower, the forced lower envelope bounds the
midpoint strength view from below. -/
theorem credal_projection_tower_lower_le_midpoint
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω) :
    t.toTypedITV.lower ≤ t.midpointDisplay :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.lower_le_midpointDisplay t

/-- In the credal projection tower, the midpoint strength view is bounded from
above by the forced upper envelope. -/
theorem credal_projection_tower_midpoint_le_upper
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower Ω) :
    t.midpointDisplay ≤ t.toTypedITV.upper :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.CredalProjectionTower.midpointDisplay_le_upper t

/-- Typed STV canary: strength does not determine displayed confidence. -/
theorem typed_stv_same_strength_can_have_different_confidence :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 2 2)
    x.strength = y.strength ∧ x.confidence.display ≠ y.confidence.display :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.same_strength_can_have_different_confidence

/-- Typed STV canary: displayed confidence does not determine strength. -/
theorem typed_stv_same_confidence_can_have_different_strength :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 2 0)
    x.confidence.display = y.confidence.display ∧ x.strength ≠ y.strength :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.TypedSTV.same_confidence_can_have_different_strength

/-- PLN simple strength is exactly the improper/Haldane Beta-posterior mean
projection of the same binary counts. -/
theorem binary_counts_improper_posterior_strength_eq_mle
    (e : Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts) :
    Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
        Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.improper e =
      e.mleStrength :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength_improper_eq_mle e

/-- Any contextual Beta-posterior mean strength is unit-bounded when its
posterior denominator is positive. -/
theorem binary_counts_posterior_mean_strength_in_unit
    (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
    (e : Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts)
    (hden :
      0 <
        Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorDenom ctx e) :
    0 ≤
        Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength ctx e ∧
      Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength ctx e ≤ 1 :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength_in_unit_of_pos_denom
    ctx e hden

/-- Context choice is a real degree of freedom for displayed strength: the same
one-positive-observation counts display as `1` under MLE/improper strength and
`2/3` under the uniform Beta-posterior projection. -/
theorem binary_counts_uniform_prior_changes_displayed_strength :
    Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.singlePositive.mleStrength = 1 ∧
      Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
          Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.singlePositive =
        (2 / 3 : ℝ) ∧
        Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.singlePositive.mleStrength ≠
          Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
            Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.singlePositive :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.singlePositive_uniform_prior_changes_strength

/-- The real-valued `BinaryCounts` MLE projection agrees with the existing
Nat-count Haldane/PLN ledger. -/
theorem binary_counts_of_nat_mle_eq_haldane
    (nPos nNeg : ℕ) :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength =
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predHaldane nPos nNeg :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts_mleStrength_eq_predHaldane
    nPos nNeg

/-- The real-valued `BinaryCounts` uniform-prior posterior projection agrees
with the existing Nat-count Laplace ledger. -/
theorem binary_counts_of_nat_uniform_eq_laplace
    (nPos nNeg : ℕ) :
    Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
        Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
        (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg) =
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predLaplace nPos nNeg :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts_uniformPosterior_eq_predLaplace
    nPos nNeg

/-- The real-valued `BinaryCounts` Jeffreys-prior posterior projection agrees
with the existing Nat-count Jeffreys/KT ledger. -/
theorem binary_counts_of_nat_jeffreys_eq_kt
    (nPos nNeg : ℕ) :
    Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
        Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys
        (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg) =
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.predJeffreys nPos nNeg :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts_jeffreysPosterior_eq_predJeffreys
    nPos nNeg

/-- Small-sample prior choice matters at the `BinaryCounts` tower boundary. -/
theorem binary_counts_of_nat_prior_matters_example :
    (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 0 1).mleStrength = 0 ∧
      Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys
          (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 0 1) =
        (1 / 4 : ℝ) ∧
        Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
            (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts 0 1) =
          (1 / 3 : ℝ) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts_prior_matters_example

/-- Laplace/uniform smoothing differs from Haldane/PLN strength by the
existing `O(1/n)` bound, lifted to `BinaryCounts`. -/
theorem binary_counts_haldane_vs_laplace_difference
    (nPos nNeg : ℕ) (h : nPos + nNeg ≠ 0) :
    |(Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength -
        Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.uniform
          (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg)| ≤
      2 / ((nPos : ℝ) + (nNeg : ℝ) + 2) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts_haldane_vs_laplace_difference
    nPos nNeg h

/-- Jeffreys/KT smoothing differs from Haldane/PLN strength by the existing
`O(1/n)` bound, lifted to `BinaryCounts`. -/
theorem binary_counts_haldane_vs_jeffreys_difference
    (nPos nNeg : ℕ) (h : nPos + nNeg ≠ 0) :
    |(Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength -
        Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext.jeffreys
          (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg)| ≤
      1 / (2 * ((nPos : ℝ) + (nNeg : ℝ) + 1)) :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts_haldane_vs_jeffreys_difference
    nPos nNeg h

/-- Proper symmetric-prior posterior means converge to Haldane/PLN strength as
sample size grows, lifted to the `BinaryCounts` boundary. -/
theorem binary_counts_mle_converges_to_symmetric_posterior_mean :
    ∀ ε : ℝ, 0 < ε → ∀ priorParam : ℝ, 0 < priorParam →
      ∃ N : ℕ, ∀ nPos nNeg : ℕ, nPos + nNeg ≥ N → nPos + nNeg ≠ 0 →
        let strength :=
          (Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength
        let mean :=
          ((nPos : ℝ) + priorParam) /
            ((nPos : ℝ) + (nNeg : ℝ) + 2 * priorParam)
        |strength - mean| < ε :=
  Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts.ofNatCounts_mle_converges_to_symmetric_posterior_mean


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
