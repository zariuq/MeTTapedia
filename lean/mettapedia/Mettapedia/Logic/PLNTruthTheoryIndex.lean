import Mettapedia.Logic.PLNTruthTower
import Mettapedia.Logic.PLNConfidenceWeightRevision
import Mettapedia.Logic.PLNInformationGeometry
import Mettapedia.Logic.PLNAmplitudePhase
import Mettapedia.Logic.PLNDidacticWitnesses
import Mettapedia.Logic.PeTTaLibPLNTruthFunctions
import Mettapedia.Logic.PLNWorldModelITV
import Mettapedia.Logic.ConceptOntology.ConstructionBasePredictiveITV
import Mettapedia.Logic.WalleyMultinomialIDMExamples
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
import Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
import Mettapedia.Logic.MarkovLogicPLNTruthBridge
import Mettapedia.Logic.MarkovLogicInfiniteUniqueness
import Mettapedia.Logic.MarkovLogicInfinitePLNCrown
import Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample
import Mettapedia.Logic.DeFinettiProjectiveCredalBridge

/-!
# PLN Truth Theory Index

This file is a theorem index for the confidence / strength / ITV tower.  It
does not add new mathematical content; it gives stable, reader-facing names for
the main theorem families:

* reconstructive confidence coordinates;
* freedom/canaries for confidence and ITV projections;
* information-geometric mean/concentration coordinates;
* typed binary and categorical revision;
* Walley-IDM bridge laws.
-/

namespace Mettapedia.Logic.PLNTruthTheoryIndex

open Mettapedia.Logic.PLNConfidenceWeight
open Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.Logic.PLNIndefiniteTruth
open Mettapedia.Logic.PLNInformationGeometry
open Mettapedia.Logic.PLNAmplitudePhase
open Mettapedia.Logic.PLNTruthTower
open Mettapedia.Algebra.TwoDimClassification
open scoped ENNReal

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
    (a b c ba bc : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction a b c ba bc).c =
      Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
        (min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w ba.c)
          (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w bc.c)) :=
  Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction_c_eq_weight_min
    a b c ba bc

/-- The PeTTa abduction mirror uses the intended weight-space minimum for
confidence. -/
theorem petta_abduction_confidence_is_weight_min
    (a b c ab cb : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction a b c ab cb).c =
      Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
        (min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w ab.c)
          (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w cb.c)) :=
  Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction_c_eq_weight_min
    a b c ab cb

/-- Weight-space minimum collapses to raw minimum only after PeTTa's confidence
cap is made explicit. -/
theorem petta_weight_min_collapses_to_min_capped_confidence (c₁ c₂ : ℝ) :
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
        (min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w c₁)
          (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w c₂)) =
      min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf c₁)
        (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf c₂) :=
  Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c_min_c2w c₁ c₂

/-- PeTTa revision confidence is weight addition transported back through
`w2c`, with the mirror's final cap retained. -/
theorem petta_revision_confidence_is_weight_addition
    (t₁ t₂ : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthRevision t₁ t₂).c =
      min 1 (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
        (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w t₁.c +
          Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w t₂.c)) := by
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthRevision]

/-- PeTTa negation preserves confidence exactly. -/
theorem petta_negation_preserves_confidence
    (t : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthNegation t).c = t.c := by
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthNegation]

/-- PeTTa modus ponens multiplies premise confidences; this is a different
rule shape from the induction/abduction weight-space minimum. -/
theorem petta_modus_ponens_confidence_is_product
    (p pq : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV) :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c =
      p.c * pq.c := by
  simp [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens]

/-- Concrete canary: on two half-confident premises, PeTTa modus ponens'
product rule is strictly below raw minimum. -/
theorem petta_modus_ponens_product_below_min_canary :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens
        ⟨0, 0.5⟩ ⟨0, 0.5⟩).c <
      min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf 0.5)
        (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf 0.5) := by
  norm_num [Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens,
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf,
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.MAX_CONF]

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
      Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ∧
        Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv ∧
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
            Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv :=
  genericITV_point_projection_not_forced

/-! ## Strength projection views -/

/-- For any typed ITV, the current midpoint strength view lies above the lower
endpoint. -/
theorem typed_itv_lower_le_midpoint
    {Sem : Mettapedia.Logic.PLNTruthTower.ITVSemantics}
    (x : Mettapedia.Logic.PLNTruthTower.TypedITV Sem) :
    x.lower ≤ x.midpoint :=
  Mettapedia.Logic.PLNTruthTower.TypedITV.lower_le_midpoint x

/-- For any typed ITV, the current midpoint strength view lies below the upper
endpoint. -/
theorem typed_itv_midpoint_le_upper
    {Sem : Mettapedia.Logic.PLNTruthTower.ITVSemantics}
    (x : Mettapedia.Logic.PLNTruthTower.TypedITV Sem) :
    x.midpoint ≤ x.upper :=
  Mettapedia.Logic.PLNTruthTower.TypedITV.midpoint_le_upper x

/-- For any typed ITV, the current midpoint strength view is unit-bounded. -/
theorem typed_itv_midpoint_in_unit
    {Sem : Mettapedia.Logic.PLNTruthTower.ITVSemantics}
    (x : Mettapedia.Logic.PLNTruthTower.TypedITV Sem) :
    x.midpoint ∈ Set.Icc (0 : ℝ) 1 :=
  Mettapedia.Logic.PLNTruthTower.TypedITV.midpoint_in_unit x

/-- In the credal projection tower, midpoint strength is exactly the average of
the forced lower/upper credal envelope. -/
theorem credal_projection_tower_midpoint_is_envelope_average
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω) :
    t.midpointDisplay =
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          t.credal t.gamble +
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          t.credal t.gamble) / 2 :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.midpointDisplay_eq_credal_average t

/-- In the credal projection tower, the forced lower envelope bounds the
midpoint strength view from below. -/
theorem credal_projection_tower_lower_le_midpoint
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω) :
    t.toTypedITV.lower ≤ t.midpointDisplay :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.lower_le_midpointDisplay t

/-- In the credal projection tower, the midpoint strength view is bounded from
above by the forced upper envelope. -/
theorem credal_projection_tower_midpoint_le_upper
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω) :
    t.midpointDisplay ≤ t.toTypedITV.upper :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.midpointDisplay_le_upper t

/-- Typed STV canary: strength does not determine displayed confidence. -/
theorem typed_stv_same_strength_can_have_different_confidence :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 2 2)
    x.strength = y.strength ∧ x.confidence.display ≠ y.confidence.display :=
  Mettapedia.Logic.PLNTruthTower.TypedSTV.same_strength_can_have_different_confidence

/-- Typed STV canary: displayed confidence does not determine strength. -/
theorem typed_stv_same_confidence_can_have_different_strength :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 2 0)
    x.confidence.display = y.confidence.display ∧ x.strength ≠ y.strength :=
  Mettapedia.Logic.PLNTruthTower.TypedSTV.same_confidence_can_have_different_strength

/-- PLN simple strength is exactly the improper/Haldane Beta-posterior mean
projection of the same binary counts. -/
theorem binary_counts_improper_posterior_strength_eq_mle
    (e : Mettapedia.Logic.PLNTruthTower.BinaryCounts) :
    Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
        Mettapedia.Logic.EvidenceClass.BinaryContext.improper e =
      e.mleStrength :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength_improper_eq_mle e

/-- Any contextual Beta-posterior mean strength is unit-bounded when its
posterior denominator is positive. -/
theorem binary_counts_posterior_mean_strength_in_unit
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
    (e : Mettapedia.Logic.PLNTruthTower.BinaryCounts)
    (hden :
      0 <
        Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorDenom ctx e) :
    0 ≤
        Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength ctx e ∧
      Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength ctx e ≤ 1 :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength_in_unit_of_pos_denom
    ctx e hden

/-- Context choice is a real degree of freedom for displayed strength: the same
one-positive-observation counts display as `1` under MLE/improper strength and
`2/3` under the uniform Beta-posterior projection. -/
theorem binary_counts_uniform_prior_changes_displayed_strength :
    Mettapedia.Logic.PLNTruthTower.BinaryCounts.singlePositive.mleStrength = 1 ∧
      Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
          Mettapedia.Logic.PLNTruthTower.BinaryCounts.singlePositive =
        (2 / 3 : ℝ) ∧
        Mettapedia.Logic.PLNTruthTower.BinaryCounts.singlePositive.mleStrength ≠
          Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
            Mettapedia.Logic.PLNTruthTower.BinaryCounts.singlePositive :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.singlePositive_uniform_prior_changes_strength

/-- The real-valued `BinaryCounts` MLE projection agrees with the existing
Nat-count Haldane/PLN ledger. -/
theorem binary_counts_of_nat_mle_eq_haldane
    (nPos nNeg : ℕ) :
    (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength =
      Mettapedia.Logic.EvidenceBeta.predHaldane nPos nNeg :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts_mleStrength_eq_predHaldane
    nPos nNeg

/-- The real-valued `BinaryCounts` uniform-prior posterior projection agrees
with the existing Nat-count Laplace ledger. -/
theorem binary_counts_of_nat_uniform_eq_laplace
    (nPos nNeg : ℕ) :
    Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
        Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
        (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg) =
      Mettapedia.Logic.EvidenceBeta.predLaplace nPos nNeg :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts_uniformPosterior_eq_predLaplace
    nPos nNeg

/-- The real-valued `BinaryCounts` Jeffreys-prior posterior projection agrees
with the existing Nat-count Jeffreys/KT ledger. -/
theorem binary_counts_of_nat_jeffreys_eq_kt
    (nPos nNeg : ℕ) :
    Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
        Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
        (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg) =
      Mettapedia.Logic.EvidenceBeta.predJeffreys nPos nNeg :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts_jeffreysPosterior_eq_predJeffreys
    nPos nNeg

/-- Small-sample prior choice matters at the `BinaryCounts` tower boundary. -/
theorem binary_counts_of_nat_prior_matters_example :
    (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 0 1).mleStrength = 0 ∧
      Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
          (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 0 1) =
        (1 / 4 : ℝ) ∧
        Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
            (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 0 1) =
          (1 / 3 : ℝ) :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts_prior_matters_example

/-- Laplace/uniform smoothing differs from Haldane/PLN strength by the
existing `O(1/n)` bound, lifted to `BinaryCounts`. -/
theorem binary_counts_haldane_vs_laplace_difference
    (nPos nNeg : ℕ) (h : nPos + nNeg ≠ 0) :
    |(Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength -
        Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
          (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg)| ≤
      2 / ((nPos : ℝ) + (nNeg : ℝ) + 2) :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts_haldane_vs_laplace_difference
    nPos nNeg h

/-- Jeffreys/KT smoothing differs from Haldane/PLN strength by the existing
`O(1/n)` bound, lifted to `BinaryCounts`. -/
theorem binary_counts_haldane_vs_jeffreys_difference
    (nPos nNeg : ℕ) (h : nPos + nNeg ≠ 0) :
    |(Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength -
        Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
          (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg)| ≤
      1 / (2 * ((nPos : ℝ) + (nNeg : ℝ) + 1)) :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts_haldane_vs_jeffreys_difference
    nPos nNeg h

/-- Proper symmetric-prior posterior means converge to Haldane/PLN strength as
sample size grows, lifted to the `BinaryCounts` boundary. -/
theorem binary_counts_mle_converges_to_symmetric_posterior_mean :
    ∀ ε : ℝ, 0 < ε → ∀ priorParam : ℝ, 0 < priorParam →
      ∃ N : ℕ, ∀ nPos nNeg : ℕ, nPos + nNeg ≥ N → nPos + nNeg ≠ 0 →
        let strength :=
          (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength
        let mean :=
          ((nPos : ℝ) + priorParam) /
            ((nPos : ℝ) + (nNeg : ℝ) + 2 * priorParam)
        |strength - mean| < ε :=
  Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts_mle_converges_to_symmetric_posterior_mean

/-! ## Typed ITV constructor provenance -/

/-- Raw ITV fields are not constructor provenance: the same displayed interval
can be carried under different typed semantics. -/
theorem raw_itv_fields_do_not_identify_constructor_provenance :
    let raw := ITV.fullWidthWithCredibility 0 (by norm_num)
    let generic : TypedITV genericITVSemantics := TypedITV.fromGeneric raw
    let walley : TypedITV (walleyBinaryITVSemantics 1) :=
      TypedITV.fromWalleyBinary 1 (by norm_num)
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.zero
    generic.lower = walley.lower ∧
      generic.upper = walley.upper ∧
        generic.credibility = walley.credibility :=
  TypedITV.generic_and_walley_zero_can_share_raw_fields

/-- The typed Walley binary constructor carries the width-complement law. -/
theorem typed_walley_binary_has_width_complement
    (s : ℝ) (hs : 0 < s)
    (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) :
    (TypedITV.fromWalleyBinary s hs e).width +
      (TypedITV.fromWalleyBinary s hs e).credibility = 1 :=
  TypedITV.walleyBinary_width_add_credibility s hs e

/-- The typed Bayesian credible constructor keeps credibility tied to evidence
concentration at the fixed prior context. -/
theorem typed_bayes_credible_credibility_is_evidence_concentration
    (backend : Mettapedia.Logic.EvidenceBeta.CredibleIntervalBackend)
    (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
    (level : ℝ) (hlevel : 0 < level ∧ level < 1)
    (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence) :
    (TypedITV.fromBayesCredible backend ctx level hlevel e).credibility =
      (Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toConfidence
        (ctx.α₀ + ctx.β₀) e).toReal :=
  TypedITV.bayesCredible_credibility_eq backend ctx level hlevel e

/-- The typed Walley categorical constructor carries the same
width-complement law as the binary IDM slice. -/
theorem typed_walley_categorical_has_width_complement
    {k : ℕ} (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (TypedITV.fromWalleyCategorical ctx e i).width +
      (TypedITV.fromWalleyCategorical ctx e i).credibility = 1 :=
  TypedITV.walleyCategorical_width_add_credibility ctx e i

/-- The typed Walley categorical constructor's credibility is the IDM
precision proxy determined by total categorical evidence and IDM strength. -/
theorem typed_walley_categorical_credibility_is_idm_precision
    {k : ℕ} (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k) :
    (TypedITV.fromWalleyCategorical ctx e i).credibility =
      (e.total : ℝ) /
        Mettapedia.Logic.EvidenceDirichlet.idmDenom ctx e :=
  TypedITV.walleyCategorical_credibility_eq ctx e i

/-- In a nondegenerate categorical carrier, the typed Walley categorical ITV
width is exactly the credal-set lower/upper envelope width for the queried
category. -/
theorem typed_walley_categorical_width_matches_credal_envelope
    {k : ℕ} (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (i j : Fin k) (hji : j ≠ i) :
    (TypedITV.fromWalleyCategorical ctx e i).width =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) -
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) :=
  TypedITV.walleyCategorical_width_eq_credal_width_of_other ctx e i j hji

/-! ## Typed ITV operation compatibility -/

/-- Same-semantics typed conjunction is available without discarding
provenance, but its result has derived-operation provenance rather than
pretending to be a fresh value of the original constructor semantics. -/
theorem typed_itv_same_semantics_conjunction_raw_value
    {Sem : ITVSemantics} (x y : TypedITV Sem) :
    (TypedITV.conjunctionSameSemantics x y).value =
      ITV.conjunction x.value y.value :=
  TypedITV.value_conjunctionSameSemantics x y

/-- Same-semantics typed implication is also a derived-operation value, not a
silent reuse of the input constructor semantics. -/
theorem typed_itv_same_semantics_implication_raw_value
    {Sem : ITVSemantics} (x y : TypedITV Sem) :
    (TypedITV.implicationSameSemantics x y).value =
      ITV.implication x.value y.value :=
  TypedITV.value_implicationSameSemantics x y

/-- Forgetting into the generic raw-ITV semantics preserves displayed fields,
but it is an explicit operation so constructor provenance is not silently
mixed. -/
theorem typed_itv_forget_to_generic_preserves_raw_value
    {Sem : ITVSemantics} (x : TypedITV Sem) :
    (TypedITV.forgetToGeneric x).value = x.value :=
  TypedITV.value_forgetToGeneric x

/-- Cross-semantics conjunction is routed through an explicit bridge to a
shared target semantics. -/
theorem typed_itv_cross_semantics_conjunction_via_bridge_raw_value
    {Sem₁ Sem₂ Target : ITVSemantics}
    (B : TypedITV.Bridge Sem₁ Sem₂ Target)
    (x : TypedITV Sem₁) (y : TypedITV Sem₂) :
    (TypedITV.conjunctionViaBridge B x y).value =
      ITV.conjunction (B.left x).value (B.right y).value :=
  TypedITV.value_conjunctionViaBridge B x y

/-! ## Forced categorical queries -/

/-- Categorical query means are forced by the retained aggregate
`MultiEvidence`. -/
theorem categorical_query_mean_is_forced_by_aggregate
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
  categoricalSurface_queryMean_forced_by_aggregate S i h

/-- Categorical IDM interval endpoints and width are forced by the retained
aggregate `MultiEvidence`, once the IDM context and category are chosen. -/
theorem categorical_idm_envelope_is_forced_by_aggregate
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
  categoricalSurface_idmEnvelope_forced_by_aggregate S ctx i h

/-! ## Sufficient-statistic strength and confidence queries -/

/-- Strength and confidence are views forced by retained evidence.  The
confidence scale, IDM context, and queried category are chosen parameters of
the view; once chosen, equal retained evidence forces equal answers. -/
structure SufficientStatisticQueryProfile where
  binaryWorldStrengthForced :
    ∀ {State Query : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      {W₁ W₂ : State} {q : Query},
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₁ q =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₂ q →
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength
            (State := State) (Query := Query) W₁ q =
          Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength
            (State := State) (Query := Query) W₂ q
  binaryWorldConfidenceForced :
    ∀ {State Query : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (κ : ℝ≥0∞) {W₁ W₂ : State} {q : Query},
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₁ q =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.evidence
          (State := State) (Query := Query) W₂ q →
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryConfidence
            (State := State) (Query := Query) κ W₁ q =
          Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryConfidence
            (State := State) (Query := Query) κ W₂ q
  binarySurfaceStrengthForced :
    ∀ {Obs Query : Type}
      (S :
        Mettapedia.Logic.SufficientStatisticSurface Obs Query
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
      {σ₁ σ₂ : Multiset Obs} {q : Query},
      Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q →
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength
            (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q) =
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength
            (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q)
  binarySurfaceConfidenceForced :
    ∀ {Obs Query : Type}
      (S :
        Mettapedia.Logic.SufficientStatisticSurface Obs Query
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
      (κ : ℝ≥0∞) {σ₁ σ₂ : Multiset Obs} {q : Query},
      Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q →
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toConfidence κ
            (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q) =
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toConfidence κ
            (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q)
  categoricalMeanForced :
    ∀ {Obs Query : Type} {k : ℕ}
      (S :
        Mettapedia.Logic.SufficientStatisticSurface Obs Query
          (Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k))
      {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k),
      Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q →
        ((Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q).counts i : ℝ) /
            ((Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q).total : ℝ) =
          ((Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q).counts i : ℝ) /
            ((Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q).total : ℝ)
  categoricalIDMEnvelopeForced :
    ∀ {Obs Query : Type} {k : ℕ}
      (S :
        Mettapedia.Logic.SufficientStatisticSurface Obs Query
          (Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k))
      (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
      {σ₁ σ₂ : Multiset Obs} {q : Query} (i : Fin k),
      Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₁ q =
        Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q →
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
                (Mettapedia.Logic.SufficientStatisticSurface.aggregate S σ₂ q)

/-- Sufficient-statistic query profile for strength, confidence, categorical
means, and categorical IDM envelopes. -/
def sufficientStatisticQueryProfile : SufficientStatisticQueryProfile where
  binaryWorldStrengthForced := by
    intro State Query instEvidence instWM W₁ W₂ q h
    exact
      Mettapedia.Logic.PLNForcedQueries.queryStrength_eq_of_same_evidence h
  binaryWorldConfidenceForced := by
    intro State Query instEvidence instWM κ W₁ W₂ q h
    exact
      Mettapedia.Logic.PLNForcedQueries.queryConfidence_eq_of_same_evidence
        κ h
  binarySurfaceStrengthForced := by
    intro Obs Query S σ₁ σ₂ q h
    exact
      Mettapedia.Logic.PLNForcedQueries.binarySurface_strength_eq_of_same_aggregate
        S h
  binarySurfaceConfidenceForced := by
    intro Obs Query S κ σ₁ σ₂ q h
    exact
      Mettapedia.Logic.PLNForcedQueries.binarySurface_confidence_eq_of_same_aggregate
        S κ h
  categoricalMeanForced := by
    intro Obs Query k S σ₁ σ₂ q i h
    exact categorical_query_mean_is_forced_by_aggregate S i h
  categoricalIDMEnvelopeForced := by
    intro Obs Query k S ctx σ₁ σ₂ q i h
    exact categorical_idm_envelope_is_forced_by_aggregate S ctx i h

/-! ## Credal and lower-prevision forced queries -/

/-- Lower expectation is a forced projection of a retained credal set. -/
theorem credal_lower_expectation_is_forced_by_credal_set
    {World Ω : Type*} [Fintype Ω]
    (credal :
      World →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    {W₁ W₂ : World} (h : credal W₁ = credal W₂) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (credal W₁) f =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (credal W₂) f :=
  Mettapedia.Logic.PLNForcedQueries.credalLower_eq_of_same_credalSet
    credal f h

/-- Upper expectation is a forced projection of a retained credal set. -/
theorem credal_upper_expectation_is_forced_by_credal_set
    {World Ω : Type*} [Fintype Ω]
    (credal :
      World →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    {W₁ W₂ : World} (h : credal W₁ = credal W₂) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (credal W₁) f =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (credal W₂) f :=
  Mettapedia.Logic.PLNForcedQueries.credalUpper_eq_of_same_credalSet
    credal f h

/-- The full lower/upper envelope is a forced projection of a retained credal
set. -/
theorem credal_envelope_is_forced_by_credal_set
    {World Ω : Type*} [Fintype Ω]
    (credal :
      World →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    {W₁ W₂ : World} (h : credal W₁ = credal W₂) :
    (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (credal W₁) f,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (credal W₁) f) =
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (credal W₂) f,
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (credal W₂) f) :=
  Mettapedia.Logic.PLNForcedQueries.credalEnvelope_eq_of_same_credalSet
    credal f h

/-- A coherent lower-prevision value is forced by the retained lower
prevision. -/
theorem lower_prevision_value_is_forced_by_lower_prevision
    {World Ω : Type*}
    (prevision :
      World → Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    {W₁ W₂ : World} (h : prevision W₁ = prevision W₂) :
    prevision W₁ X = prevision W₂ X :=
  Mettapedia.Logic.PLNForcedQueries.lowerPrevisionValue_eq_of_same_lowerPrevision
    prevision X h

/-- The conjugate upper-prevision value is also forced by the retained lower
prevision. -/
theorem upper_prevision_value_is_forced_by_lower_prevision
    {World Ω : Type*}
    (prevision :
      World → Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    {W₁ W₂ : World} (h : prevision W₁ = prevision W₂) :
    (prevision W₁).conjugate X = (prevision W₂).conjugate X :=
  Mettapedia.Logic.PLNForcedQueries.upperPrevisionValue_eq_of_same_lowerPrevision
    prevision X h

/-- The lower prevision induced by a retained coherent desirable-gamble set is
a forced projection of that retained set. -/
theorem desirable_lower_prevision_is_forced_by_desirable_set
    {World Ω : Type*}
    (desirable :
      World →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    {W₁ W₂ : World} (h : desirable W₁ = desirable W₂) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (desirable W₁) f =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (desirable W₂) f :=
  Mettapedia.Logic.PLNForcedQueries.desirableLowerPrevision_eq_of_same_desirableSet
    desirable f h

/-! ## Credal envelopes as typed ITV views -/

/-- A finite credal-set envelope typed as an ITV has lower endpoint forced by
the retained credal set and queried gamble. -/
theorem credal_envelope_typed_itv_lower_forced
    {Ω : Type*} [Fintype Ω]
    (src : Mettapedia.Logic.PLNTruthTower.CredalEnvelopeITVSource Ω) :
    (Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope src).lower =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        src.credal src.gamble :=
  Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope_lower src

/-- A finite credal-set envelope typed as an ITV has upper endpoint forced by
the retained credal set and queried gamble. -/
theorem credal_envelope_typed_itv_upper_forced
    {Ω : Type*} [Fintype Ω]
    (src : Mettapedia.Logic.PLNTruthTower.CredalEnvelopeITVSource Ω) :
    (Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope src).upper =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        src.credal src.gamble :=
  Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope_upper src

/-- The typed credal-envelope ITV records the selected credibility coordinate
explicitly rather than deriving it from the lower/upper envelope. -/
theorem credal_envelope_typed_itv_credibility_is_selected
    {Ω : Type*} [Fintype Ω]
    (src : Mettapedia.Logic.PLNTruthTower.CredalEnvelopeITVSource Ω) :
    (Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope src).credibility =
      src.credibility :=
  Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope_credibility src

/-- Credal lower/upper endpoints do not force the credibility coordinate. -/
theorem credal_envelope_bounds_do_not_force_confidence_coordinate
    {Ω : Type*} [Fintype Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    let x : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
      Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope
        { credal := K
          gamble := f
          credal_nonempty := hK
          gamble_in_unit := hf
          credibility := 0
          credibility_in_unit := by norm_num }
    let y : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
      Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope
        { credal := K
          gamble := f
          credal_nonempty := hK
          gamble_in_unit := hf
          credibility := 1
          credibility_in_unit := by norm_num }
    x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility :=
  Mettapedia.Logic.PLNTruthTower.credalEnvelope_bounds_do_not_force_credibility K hK f hf

/-! ## Abstract lower-prevision envelopes as typed ITV views -/

/-- A lower-prevision envelope typed as an ITV has lower endpoint forced by
the retained lower prevision and queried gamble. -/
theorem lower_prevision_typed_itv_lower_forced
    {Ω : Type*}
    (src : Mettapedia.Logic.PLNTruthTower.LowerPrevisionITVSource Ω) :
    (Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision src).lower =
      src.prevision src.gamble :=
  Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision_lower src

/-- A lower-prevision envelope typed as an ITV has upper endpoint forced by
the conjugate upper prevision and queried gamble. -/
theorem lower_prevision_typed_itv_upper_forced
    {Ω : Type*}
    (src : Mettapedia.Logic.PLNTruthTower.LowerPrevisionITVSource Ω) :
    (Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision src).upper =
      src.prevision.conjugate src.gamble :=
  Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision_upper src

/-- The typed lower-prevision ITV records the selected credibility coordinate
explicitly rather than deriving it from the lower/upper envelope. -/
theorem lower_prevision_typed_itv_credibility_is_selected
    {Ω : Type*}
    (src : Mettapedia.Logic.PLNTruthTower.LowerPrevisionITVSource Ω) :
    (Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision src).credibility =
      src.credibility :=
  Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision_credibility src

/-- Abstract lower-prevision lower/upper endpoints do not force the credibility
coordinate. -/
theorem lower_prevision_bounds_do_not_force_confidence_coordinate
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    let x : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
      Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision
        { prevision := P
          gamble := X
          gamble_in_unit := hX
          credibility := 0
          credibility_in_unit := by norm_num }
    let y : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
      Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision
        { prevision := P
          gamble := X
          gamble_in_unit := hX
          credibility := 1
          credibility_in_unit := by norm_num }
    x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility :=
  Mettapedia.Logic.PLNTruthTower.lowerPrevision_bounds_do_not_force_credibility
    P X hX

/-- Singleton finite credal envelopes agree with the precise lower-prevision
ITV induced by the singleton probability distribution. -/
theorem singleton_credal_lower_prevision_itv_agrees
    {Ω : Type*} [Fintype Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.ProbDist Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let lp : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
      Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision
        (Mettapedia.Logic.PLNTruthTower.SingletonCredalLowerPrevision.source
          P X hX credibility hc);
    let ce : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
      Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope
        (Mettapedia.Logic.PLNTruthTower.SingletonCredalLowerPrevision.credalEnvelopeSource
          P X hX credibility hc);
    lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
      lp.credibility = ce.credibility :=
  Mettapedia.Logic.PLNTruthTower.SingletonCredalLowerPrevision.typedLowerPrevision_agrees_with_singletonCredalEnvelope
    P X hX credibility hc

/-- Finite credal envelopes agree with the lower-prevision ITV induced by the
finite credal lower envelope. -/
theorem finite_credal_lower_prevision_itv_agrees
    {Ω : Type*} [Fintype Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let lp : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
      Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision
        (Mettapedia.Logic.PLNTruthTower.FiniteCredalLowerPrevision.source
          K hK X hX credibility hc);
    let ce : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
      Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope
        { credal := K
          gamble := X
          credal_nonempty := hK
          gamble_in_unit := hX
          credibility := credibility
          credibility_in_unit := hc };
    lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
      lp.credibility = ce.credibility :=
  Mettapedia.Logic.PLNTruthTower.FiniteCredalLowerPrevision.typedLowerPrevision_agrees_with_credalEnvelope
    K hK X hX credibility hc

/-! ## Credal projection tower: forced envelope plus selected confidence -/

/-- In the credal projection tower, lower is forced by the retained credal set
and queried gamble. -/
theorem credal_projection_tower_lower_forced
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω) :
    t.toTypedITV.lower =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        t.credal t.gamble :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.lower_toTypedITV t

/-- In the credal projection tower, upper is forced by the retained credal set
and queried gamble. -/
theorem credal_projection_tower_upper_forced
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω) :
    t.toTypedITV.upper =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        t.credal t.gamble :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.upper_toTypedITV t

/-- In the credal projection tower, displayed credibility is selected by the
chosen evidence-weight coordinate and evidence weight. -/
theorem credal_projection_tower_credibility_selected
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω) :
    t.toTypedITV.credibility = t.coordinate.encode t.weight :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.credibility_toTypedITV t

/-- The tower's typed confidence decodes back to the selected evidence weight. -/
theorem credal_projection_tower_confidence_decodes_weight
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω) :
    t.typedConfidence.weight = t.weight :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.typedConfidence_weight t

/-- The width-complement bridge, when explicitly assumed, forces the selected
display to be the complement of credal width. -/
theorem credal_projection_width_complement_bridge_forces_display
    {Ω : Type*} [Fintype Ω]
    (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω)
    (h : t.WidthComplementBridge) :
    t.credibilityDisplay = 1 - t.toTypedITV.width :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.widthComplementBridge_forces_display t h

/-- Same credal envelope and same evidence weight can still display different
credibilities when the coordinate choice differs. -/
theorem credal_projection_same_weight_can_display_different_confidence
    {Ω : Type*} [Fintype Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1) :
    let x : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K
        credal_nonempty := hK
        gamble := f
        gamble_in_unit := hf
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    let y : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
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
      x.typedConfidence.weight = y.typedConfidence.weight :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.same_weight_can_display_different_credibility
    K hK f hf

/-- Same coordinate and same evidence weight force the same displayed
credibility, independently of the retained credal envelope. -/
theorem credal_projection_same_coordinate_weight_forces_same_confidence
    {Ω : Type*} [Fintype Ω]
    (K₁ K₂ :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
    (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc 0 1)
    (χ : EvidenceWeightCoordinate) (hχ : UnitIcoOnNonneg χ)
    (w : ℝ) (hw : 0 ≤ w) :
    let x : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K₁
        credal_nonempty := hK₁
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    let y : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K₂
        credal_nonempty := hK₂
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.same_coordinate_weight_forces_same_confidence
    K₁ K₂ hK₁ hK₂ f hf χ hχ w hw

/-- Same coordinate and same evidence weight can coexist with a different credal
envelope; a changed lower envelope leaves displayed confidence untouched. -/
theorem credal_projection_same_confidence_can_have_different_envelope
    {Ω : Type*} [Fintype Ω]
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
    let x : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
      { credal := K₁
        credal_nonempty := hK₁
        gamble := f
        gamble_in_unit := hf
        coordinate := χ
        coordinate_unit := hχ
        weight := w
        weight_nonneg := hw }
    let y : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
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
        x.toTypedITV.lower ≠ y.toTypedITV.lower :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.same_confidence_can_have_different_credal_envelope
    K₁ K₂ hK₁ hK₂ f hf χ hχ w hw hLower

/-- Concrete Bool witness for the projection tower: same confidence coordinate
and evidence weight, but different lower credal envelopes. -/
theorem credal_projection_bool_same_confidence_different_envelope :
    let x : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Bool :=
      { credal := Set.singleton
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolFalseProbDist
        credal_nonempty :=
          ⟨Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolFalseProbDist, rfl⟩
        gamble :=
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTruthGamble
        gamble_in_unit :=
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    let y : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Bool :=
      { credal := Set.singleton
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTrueProbDist
        credal_nonempty :=
          ⟨Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTrueProbDist, rfl⟩
        gamble :=
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTruthGamble
        gamble_in_unit :=
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight ∧
      x.toTypedITV.lower = 0 ∧
      y.toTypedITV.lower = 1 ∧
      x.toTypedITV.lower ≠ y.toTypedITV.lower :=
  Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.concreteBool_same_confidence_different_credal_envelope

/-! ## Coherent desirable-gamble / lower-prevision forced queries -/

/-- A coherent desirable-gamble set avoids sure loss: no strictly negative
gamble is desirable. -/
theorem coherent_desirable_set_avoids_sure_loss
    {Ω : Type*}
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    ∀ f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω,
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble.StrictlyNegative f →
        f ∉ C.D :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.avoid_sure_loss C

/-- A coherent desirable-gamble set is a positive convex cone. -/
theorem coherent_desirable_set_is_positive_cone
    {Ω : Type*}
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    ∀ f g :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω,
      f ∈ C.D → g ∈ C.D → ∀ a b : ℝ, a > 0 → b > 0 →
        a • f + b • g ∈ C.D :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.desirable_is_cone C

/-- Coherent lower previsions are monotone. -/
theorem lower_prevision_is_monotone
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    {X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω}
    (h : X ≤ Y) :
    P X ≤ P Y :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision.mono P h

/-- Coherent lower previsions are superadditive. -/
theorem lower_prevision_is_superadditive
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    P X + P Y ≤ P (X + Y) := by
  exact P.superadd X Y

/-- The conjugate upper prevision is subadditive. -/
theorem upper_conjugate_prevision_is_subadditive
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    P.conjugate (X + Y) ≤ P.conjugate X + P.conjugate Y :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision.conjugate_subadditive
    P X Y

/-- Lower-prevision imprecision is nonnegative. -/
theorem lower_prevision_imprecision_is_nonnegative
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    0 ≤ Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision P X :=
  Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision_nonneg P X

/-- A regular lower prevision induces a coherent desirable-gamble set.  This is
the proved lower-prevision-to-desirability direction; it does not assert the
full converse natural-extension theorem. -/
noncomputable def regular_lower_prevision_induces_coherent_desirable_set
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (hReg : Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet
    P hReg

/-- Membership in the desirable set induced by a regular lower prevision is
exactly strict positivity of the lower prevision. -/
theorem regular_lower_prevision_desirable_membership
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (hReg : Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    X ∈ (regular_lower_prevision_induces_coherent_desirable_set P hReg).D ↔
      P X > 0 :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet_mem
    P hReg X

/-- Finite nonempty outcome spaces make regularity automatic for every lower
prevision. -/
theorem finite_lower_prevision_is_regular
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finite_regular P

/-- The coherent desirable-gamble set induced by a lower prevision on a finite
nonempty outcome space. -/
noncomputable def finite_lower_prevision_induces_coherent_desirable_set
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
    P

/-- A finite credal lower envelope induces a coherent desirable-gamble set, and
membership is strict positivity of the lower envelope. -/
theorem finite_credal_lower_prevision_desirable_membership
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (K :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
    (hK : K.Nonempty)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    X ∈
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCredalCoherentDesirableSet
          K hK).D ↔
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K X > 0 :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCredalCoherentDesirableSet_mem
    K hK X

/-- Finite coherent desirable-gamble sets induce genuine lower previsions via
Walley's natural-extension supremum formula.  This is the proved finite
converse direction, not the full infinite-dimensional representation theorem. -/
noncomputable def finite_desirable_set_induces_lower_prevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω :=
  Mettapedia.Logic.PLNTruthTower.DesirableLowerPrevisionBridge.finiteLowerPrevision
    C

/-- The finite desirable-gamble lower prevision is definitionally the
acceptable-price supremum already used by the desirable-gamble layer. -/
theorem finite_desirable_lower_prevision_apply
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    finite_desirable_set_induces_lower_prevision C X =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X :=
  Mettapedia.Logic.PLNTruthTower.DesirableLowerPrevisionBridge.finiteLowerPrevision_apply
    C X

/-- Lower-bound law for the finite desirable-gamble natural extension. -/
theorem finite_desirable_lower_prevision_lower_bound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (c : ℝ) (hc : ∀ ω, c ≤ X ω) :
    c ≤ finite_desirable_set_induces_lower_prevision C X :=
  Mettapedia.Logic.PLNTruthTower.DesirableLowerPrevisionBridge.lowerPrevision_lower_bound
    C X c hc

/-- Positive-homogeneity law for the finite desirable-gamble natural extension. -/
theorem finite_desirable_lower_prevision_pos_homog
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (r : ℝ)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
    (hr : 0 ≤ r) :
    finite_desirable_set_induces_lower_prevision C (r • X) =
      r * finite_desirable_set_induces_lower_prevision C X :=
  Mettapedia.Logic.PLNTruthTower.DesirableLowerPrevisionBridge.lowerPrevision_pos_homog
    C r X hr

/-- Superadditivity law for the finite desirable-gamble natural extension. -/
theorem finite_desirable_lower_prevision_superadditive
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω) :
    finite_desirable_set_induces_lower_prevision C X +
      finite_desirable_set_induces_lower_prevision C Y ≤
        finite_desirable_set_induces_lower_prevision C (X + Y) :=
  Mettapedia.Logic.PLNTruthTower.DesirableLowerPrevisionBridge.lowerPrevision_superadd
    C X Y

/-- A regular lower prevision round-trips through its induced desirable-gamble
set and the acceptable-price supremum construction. -/
theorem regular_lower_prevision_desirable_roundtrip
    {Ω : Type*}
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (hReg : Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet
        P hReg) X = P X :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet_lowerPrevision_roundtrip
    P hReg X

/-- On finite nonempty outcome spaces, every lower prevision is regular, so the
lower-prevision → desirable-set → finite natural-extension round-trip recovers
the original lower prevision pointwise. -/
theorem finite_lower_prevision_desirable_roundtrip_apply
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    finite_desirable_set_induces_lower_prevision
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          P) X =
      P X :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet_lowerPrevision_roundtrip_apply
    P X

/-- On finite nonempty outcome spaces, the round-trip recovers the original
lower prevision as a structure. -/
theorem finite_lower_prevision_desirable_roundtrip
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω) :
    finite_desirable_set_induces_lower_prevision
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          P) = P :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet_lowerPrevision_roundtrip
    P

/-- The finite strict reconstruction operator: project a coherent
desirable-gamble set to its finite lower prevision, then reconstruct
`{X | P X > 0}`. -/
noncomputable def finite_strict_roundtrip
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip
    C

@[simp] theorem finite_strict_roundtrip_mem
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈ (finite_strict_roundtrip C).D ↔
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X > 0 :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_mem
    C X

/-- The strict finite reconstruction preserves the lower prevision it was built
from. -/
theorem finite_strict_roundtrip_lower_prevision_eq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    finite_desirable_set_induces_lower_prevision (finite_strict_roundtrip C) =
      finite_desirable_set_induces_lower_prevision C :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_finiteLowerPrevision_eq
    C

/-- Strict finite reconstruction factors through the finite lower-prevision
projection. -/
theorem same_finite_lower_prevision_same_strict_roundtrip_D
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (h :
      finite_desirable_set_induces_lower_prevision C =
        finite_desirable_set_induces_lower_prevision D) :
    (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision C)).D =
      (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision D)).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.same_finiteLowerPrevision_same_strictRoundTrip_D
    C D h

/-- Membership form of strict finite reconstruction factorization through the
finite lower-prevision projection. -/
theorem same_finite_lower_prevision_same_strict_roundtrip_mem_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (h :
      finite_desirable_set_induces_lower_prevision C =
        finite_desirable_set_induces_lower_prevision D)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision C)).D ↔
      X ∈
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision D)).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.same_finiteLowerPrevision_same_strictRoundTrip_mem_iff
    C D h X

/-- Finite strict reconstruction is idempotent at the membership-set level. -/
theorem finite_strict_roundtrip_idempotent_D
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    (finite_strict_roundtrip (finite_strict_roundtrip C)).D =
      (finite_strict_roundtrip C).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_idempotent_D
    C

/-- Membership form of finite strict reconstruction idempotence. -/
theorem finite_strict_roundtrip_idempotent_mem_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈ (finite_strict_roundtrip (finite_strict_roundtrip C)).D ↔
      X ∈ (finite_strict_roundtrip C).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_idempotent_mem_iff
    C X

/-- Openness/Archimedeanness for desirable-gamble sets: each desirable gamble
remains desirable after subtracting some strictly positive constant. -/
def archimedean_desirable_set
    {Ω : Type*}
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    Prop :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.ArchimedeanDesirableSet
    C

/-- The canonical finite strict representative is contained in the original
coherent desirable set. -/
theorem finite_strict_roundtrip_subset_original
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    (finite_strict_roundtrip C).D ⊆ C.D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_subset_original
    C

/-- Boundary canary for the canonical finite strict representative. -/
theorem finite_strict_roundtrip_not_mem_of_nonpositive_lower_prevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    (hBoundary :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0) :
    X ∉ (finite_strict_roundtrip C).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_not_mem_of_nonpositive_lowerPrevision
    C X hBoundary

/-- Archimedean/open coherent desirable sets are fixed by the canonical finite
strict representative at the membership level. -/
theorem finite_strict_roundtrip_mem_iff_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈ (finite_strict_roundtrip C).D ↔ X ∈ C.D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_mem_iff_of_archimedean
    C hArch X

/-- Set-level fixed-point law for Archimedean/open coherent desirable sets. -/
theorem finite_strict_roundtrip_D_eq_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C) :
    (finite_strict_roundtrip C).D = C.D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_D_eq_of_archimedean
    C hArch

/-- Structure-level fixed-point law for Archimedean/open coherent desirable
sets. -/
theorem finite_strict_roundtrip_eq_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C) :
    finite_strict_roundtrip C = C :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_eq_of_archimedean
    C hArch

/-- The canonical finite strict representative is always Archimedean/open. -/
theorem finite_strict_roundtrip_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    archimedean_desirable_set (finite_strict_roundtrip C) :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_archimedean
    C

/-- Exact fixed-point characterization of the finite strict reconstruction
operator. -/
theorem finite_strict_roundtrip_eq_iff_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    finite_strict_roundtrip C = C ↔ archimedean_desirable_set C :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_eq_iff_archimedean
    C

/-- Inclusion of desirable-gamble sets makes the induced finite lower
prevision monotone. -/
theorem finite_desirable_lower_prevision_mono_of_subset
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hCD : C.D ⊆ D.D)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    finite_desirable_set_induces_lower_prevision C X ≤
      finite_desirable_set_induces_lower_prevision D X :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteLowerPrevision_mono_of_desirable_subset
    C D hCD X

/-- Monotonicity of the canonical finite strict reconstruction operator. -/
theorem finite_strict_roundtrip_mono_D
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hCD : C.D ⊆ D.D) :
    (finite_strict_roundtrip C).D ⊆ (finite_strict_roundtrip D).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_mono_D
    C D hCD

/-- Universal property: every Archimedean/open coherent desirable subset of
`C` is contained in the canonical finite strict representative of `C`. -/
theorem finite_strict_roundtrip_greatest_archimedean_subset_D
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hDArch : archimedean_desirable_set D)
    (hDC : D.D ⊆ C.D) :
    D.D ⊆ (finite_strict_roundtrip C).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_greatest_archimedean_subset_D
    C D hDArch hDC

/-- Adjunction-style universal property: for Archimedean/open `D`, inclusion
below the canonical finite strict representative of `C` is equivalent to
inclusion below `C` itself. -/
theorem finite_strict_roundtrip_archimedean_subset_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C D :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hDArch : archimedean_desirable_set D) :
    D.D ⊆ (finite_strict_roundtrip C).D ↔ D.D ⊆ C.D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteStrictRoundTrip_archimedean_subset_iff
    C D hDArch

/-- The strict desirable set induced by the finite natural extension is always
contained in the original coherent desirable set. -/
theorem finite_desirable_roundtrip_subset_original
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω) :
    (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision C)).D ⊆ C.D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteDesirableRoundTrip_subset_original
    C

/-- Boundary canary: a gamble whose induced lower prevision is nonpositive is
not recovered by the strict desirable set `{X | P X > 0}`. -/
theorem finite_desirable_boundary_not_recovered
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
    (hBoundary :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0) :
    X ∉
      (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision C)).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.nonpositive_lowerPrevision_not_recovered_by_strict_roundtrip
    C X hBoundary

/-- Under Archimedean/open desirability, the original desirable set is contained
in the strict desirable set induced by the finite natural extension. -/
theorem original_subset_finite_desirable_roundtrip_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C) :
    C.D ⊆
      (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision C)).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.original_subset_finiteDesirableRoundTrip_of_archimedean
    C hArch

/-- For Archimedean/open coherent desirable sets, the finite
desirable-set → lower-prevision → strict-desirable-set round-trip recovers
membership exactly. -/
theorem finite_desirable_roundtrip_mem_iff_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C)
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision C)).D ↔
      X ∈ C.D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteDesirableRoundTrip_mem_iff_of_archimedean
    C hArch X

/-- For Archimedean/open coherent desirable sets, the finite round-trip recovers
the original desirable-gamble membership set. -/
theorem finite_desirable_roundtrip_D_eq_of_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
    (hArch : archimedean_desirable_set C) :
    (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision C)).D = C.D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteDesirableRoundTrip_D_eq_of_archimedean
    C hArch

/-- Finite pointwise minimum of a gamble on a nonempty finite outcome space. -/
noncomputable def finite_minimum
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) : ℝ :=
  Mettapedia.Logic.PLNTruthTower.DesirableLowerPrevisionBridge.finiteMinimum X

/-- The finite minimum is no larger than every coordinate of the gamble. -/
theorem finite_minimum_le_apply
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) (ω : Ω) :
    finite_minimum X ≤ X ω :=
  Mettapedia.Logic.PLNTruthTower.DesirableLowerPrevisionBridge.finiteMinimum_le_apply X ω

/-- The strict positive cone of gambles. -/
def strict_positive_desirable_set
    (Ω : Type*) [Nonempty Ω] :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet Ω

/-- On finite nonempty outcome spaces, the strict positive cone is
Archimedean/open. -/
theorem strict_positive_desirable_set_archimedean
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    archimedean_desirable_set (strict_positive_desirable_set Ω) :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet_archimedean

/-- Positive contrast: the strict positive cone is recovered by the finite
desirable-set → lower-prevision → strict-desirable-set round-trip. -/
theorem strict_positive_roundtrip_D_eq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision
        (strict_positive_desirable_set Ω))).D =
      (strict_positive_desirable_set Ω).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet_roundtrip_D_eq

/-- Membership version of the strict-positive positive contrast. -/
theorem strict_positive_roundtrip_mem_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision
            (strict_positive_desirable_set Ω))).D ↔
      (∀ ω, 0 < X ω) :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet_roundtrip_mem_iff X

/-- The strict positive cone induces the vacuous finite lower expectation:
the pointwise finite minimum of the gamble. -/
theorem strict_positive_lower_prevision_eq_finite_minimum
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (strict_positive_desirable_set Ω) X =
        finite_minimum X :=
  by
    simpa [strict_positive_desirable_set, finite_minimum] using
      Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.strictlyPositiveDesirableSet_lowerPrevision_eq_finiteMinimum
        X

/-- The closed positive cone of nonzero nonnegative gambles.  It is coherent
but not open/Archimedean in general. -/
def nonnegative_nonzero_desirable_set
    (Ω : Type*) [Nonempty Ω] :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroDesirableSet Ω

/-- The closed positive cone induces the same vacuous finite lower expectation:
the pointwise finite minimum of the gamble. -/
theorem nonnegative_nonzero_lower_prevision_eq_finite_minimum
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegative_nonzero_desirable_set Ω) X =
        finite_minimum X :=
  by
    simpa [nonnegative_nonzero_desirable_set, finite_minimum] using
      Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroDesirableSet_lowerPrevision_eq_finiteMinimum
        X

/-- Exact boundary-forgetting mechanism: strict and closed positive cones
induce the same finite lower prevision. -/
theorem positive_cones_induce_same_lower_prevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (strict_positive_desirable_set Ω) X =
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegative_nonzero_desirable_set Ω) X :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.positiveCones_induce_same_lowerPrevision
    X

/-- Projection-level form of the same boundary-forgetting mechanism: the
strict and closed positive cones induce the same finite lower prevision. -/
theorem positive_cones_induce_same_finite_lower_prevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    finite_desirable_set_induces_lower_prevision
        (strict_positive_desirable_set Ω) =
      finite_desirable_set_induces_lower_prevision
        (nonnegative_nonzero_desirable_set Ω) :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.positiveCones_induce_same_finiteLowerPrevision

/-- Exact finite canonicalization result: projecting the closed positive cone
to a lower prevision and reconstructing by the strict/open rule recovers the
strict positive cone. -/
theorem nonnegative_nonzero_strict_roundtrip_D_eq_strict_positive
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision
        (nonnegative_nonzero_desirable_set Ω))).D =
      (strict_positive_desirable_set Ω).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroDesirableSet_strictRoundTrip_D_eq_strictlyPositive

/-- Membership form of the finite canonicalization result. -/
theorem nonnegative_nonzero_strict_roundtrip_mem_iff
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω) :
    X ∈
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision
            (nonnegative_nonzero_desirable_set Ω))).D ↔
      (∀ ω, 0 < X ω) :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroDesirableSet_strictRoundTrip_mem_iff
    X

/-- Bool boundary gamble: zero at `false`, one at `true`. -/
def bool_boundary_gamble :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Bool :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.boolBoundaryGamble

/-- The Bool boundary gamble is desirable in the closed positive cone. -/
theorem bool_boundary_gamble_desirable :
    bool_boundary_gamble ∈ (nonnegative_nonzero_desirable_set Bool).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.boolBoundaryGamble_mem_nonnegativeNonzero

/-- The Bool boundary gamble is not desirable in the strict positive cone. -/
theorem bool_boundary_gamble_not_strict :
    bool_boundary_gamble ∉ (strict_positive_desirable_set Bool).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.boolBoundaryGamble_not_mem_strictlyPositive

/-- The strict/open and closed positive cones are genuinely different on Bool. -/
theorem bool_positive_cones_distinct :
    (strict_positive_desirable_set Bool).D ≠
      (nonnegative_nonzero_desirable_set Bool).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.strictAndClosedPositiveCones_distinct_bool

/-- Concrete non-injectivity canary for the desirable-set to finite
lower-prevision projection. -/
theorem bool_positive_cones_projection_not_injective :
    (strict_positive_desirable_set Bool).D ≠
        (nonnegative_nonzero_desirable_set Bool).D ∧
      finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Bool) =
        finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Bool) :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.bool_positiveCones_projection_not_injective

/-- The Bool boundary gamble has induced lower prevision exactly zero in the
closed positive cone. -/
theorem bool_boundary_lower_prevision_eq_zero :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegative_nonzero_desirable_set Bool) bool_boundary_gamble = 0 :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.boolBoundaryGamble_lowerPrevision_eq_zero

/-- Concrete boundary canary: a desirable boundary gamble with lower prevision
zero is dropped by the strict lower-prevision-to-desirable-set round-trip. -/
theorem bool_boundary_not_recovered_by_strict_roundtrip :
    bool_boundary_gamble ∈ (nonnegative_nonzero_desirable_set Bool).D ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (nonnegative_nonzero_desirable_set Bool) bool_boundary_gamble = 0 ∧
      bool_boundary_gamble ∉
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision
            (nonnegative_nonzero_desirable_set Bool))).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.concreteBool_boundary_desirable_not_recovered_by_strict_roundtrip

/-- The closed positive cone on Bool is not Archimedean/open. -/
theorem bool_nonnegative_nonzero_not_archimedean :
    ¬ archimedean_desirable_set (nonnegative_nonzero_desirable_set Bool) :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.nonnegativeNonzeroBool_not_archimedean

/-- Concrete set-level canary: without Archimedean openness, the finite
desirable-set → lower-prevision → strict-desirable-set round-trip need not
recover the original desirable-gamble set. -/
theorem bool_boundary_roundtrip_set_ne_original :
    (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision
        (nonnegative_nonzero_desirable_set Bool))).D ≠
      (nonnegative_nonzero_desirable_set Bool).D :=
  Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.concreteBool_boundary_roundtrip_set_ne_original

/-! ## Information-geometric coordinates -/

/-- Binary mean/concentration coordinates are lossless for positive total
evidence. -/
theorem binary_mean_concentration_is_lossless
    (e : BinaryCounts) (hTotal : e.total ≠ 0) :
    (BetaMeanConcentration.fromCounts e).decodeCounts =
      (e.nPlus, e.nMinus) :=
  BetaMeanConcentration.decode_fromCounts e hTotal

/-- Categorical mean-vector/concentration coordinates are lossless for positive
total evidence, pointwise in each category. -/
theorem categorical_mean_concentration_is_lossless
    {k : ℕ} (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (hTotal : e.total ≠ 0) (i : Fin k) :
    (DirichletMeanConcentration.fromCounts e).decodeCounts i =
      (e.counts i : ℝ) :=
  DirichletMeanConcentration.decode_fromCounts e hTotal i

/-- Mean/concentration alone does not choose the binary confidence link. -/
theorem beta_coordinate_does_not_force_confidence_link :
    let z : BetaMeanConcentration := ⟨1 / 2, 1⟩
    plnConfidenceLink 1 (by norm_num) z ≠
      reserveHalfLink 1 (by norm_num) z :=
  same_beta_coordinate_two_valid_confidence_links_differ

/-- Mean-vector/concentration alone does not choose the categorical confidence
link. -/
theorem dirichlet_coordinate_does_not_force_confidence_link :
    let z : DirichletMeanConcentration 3 := ⟨fun _ => 1 / 3, 1⟩
    dirichletPLNConfidenceLink 1 (by norm_num) z ≠
      dirichletReserveHalfLink 1 (by norm_num) z :=
  same_dirichlet_coordinate_two_valid_confidence_links_differ

/-! ## Typed revision -/

/-- Typed binary revision built from evidence counts decodes to componentwise
evidence addition. -/
theorem typed_binary_revision_is_evidence_addition
    (χ : EvidenceWeightCoordinate) (e₁ e₂ : BinaryCounts)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (hSum : e₁.total + e₂.total ≠ 0) :
    (TypedSTV.revise (TypedSTV.fromCounts χ e₁)
      (TypedSTV.fromCounts χ e₂)).decodeCounts =
        ((e₁.add e₂).nPlus, (e₁.add e₂).nMinus) :=
  typedSTV_revision_fromCounts_decodes_added_counts χ e₁ e₂ h₁ h₂ hSum

/-- Typed categorical revision built from evidence counts decodes to
componentwise categorical evidence addition. -/
theorem typed_categorical_revision_is_evidence_addition
    {k : ℕ} (χ : EvidenceWeightCoordinate)
    (e₁ e₂ : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0)
    (hSum : (e₁.total : ℝ) + (e₂.total : ℝ) ≠ 0) (i : Fin k) :
    (TypedCategoricalTruth.revise
      (TypedCategoricalTruth.fromCounts χ e₁)
      (TypedCategoricalTruth.fromCounts χ e₂)).decodeCounts i =
        ((e₁ + e₂).counts i : ℝ) :=
  typedCategorical_revision_fromCounts_decodes_added_counts
    χ e₁ e₂ h₁ h₂ hSum i

/-! ## Walley-IDM bridge laws -/

/-- The Walley binary-predictive width-complement bridge forces the PLN/NARS
odds confidence coordinate. -/
theorem walley_width_complement_forces_pln_odds
    (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s)
    (hχ : WidthComplementCompatible χ s)
    {n : ℝ} (hn : 0 ≤ n) :
    χ.encode n = (plnOddsCoordinate s hs).encode n :=
  widthComplementCompatible_forces_plnOdds χ s hs hχ hn

/-- A reconstructive coordinate need not satisfy the Walley-IDM
width-complement bridge. -/
theorem reconstructive_coordinate_need_not_be_walley_compatible
    (s : ℝ) (hs : 0 < s) :
    ¬ WidthComplementCompatible (reserveHalfCoordinate s hs) s :=
  reserveHalf_not_widthComplementCompatible s hs

/-- For a symmetric Beta prior, the posterior blend weight is exactly the PLN
odds confidence link applied to the observed concentration, with the link
scale set to the prior concentration. -/
theorem symmetric_beta_blend_weight_is_concentration_link
    (π : SymmetricBetaPrior) (e : BinaryCounts) :
    π.blendWeight e =
      plnConfidenceLink (2 * π.prior) (by nlinarith [π.prior_pos])
        (BetaMeanConcentration.fromCounts e) :=
  SymmetricBetaPrior.blendWeight_eq_plnConfidenceLink π e

/-- For a general Beta mean/concentration prior, the posterior blend weight is
exactly the PLN odds confidence link applied to the observed concentration,
with the link scale set to the prior concentration. -/
theorem general_beta_blend_weight_is_concentration_link
    (π : BetaPriorMeanConcentration) (e : BinaryCounts) :
    π.blendWeight e =
      plnConfidenceLink π.concentration π.concentration_pos
        (BetaMeanConcentration.fromCounts e) :=
  BetaPriorMeanConcentration.blendWeight_eq_plnConfidenceLink π e

/-- Symmetric Beta posterior means are empirical/prior mean blends, with blend
weight equal to the concentration confidence link. -/
theorem symmetric_beta_posterior_mean_is_concentration_blend
    (π : SymmetricBetaPrior) (e : BinaryCounts) (hTotal : e.total ≠ 0) :
    π.posteriorMean e =
      π.blendWeight e * e.strength +
        (1 - π.blendWeight e) * (1 / 2 : ℝ) :=
  SymmetricBetaPrior.posteriorMean_eq_blend_empirical_with_prior_half
    π e hTotal

/-- General Beta posterior means are empirical/prior mean blends, with blend
weight equal to the concentration confidence link. -/
theorem general_beta_posterior_mean_is_concentration_blend
    (π : BetaPriorMeanConcentration) (e : BinaryCounts)
    (hTotal : e.total ≠ 0) :
    π.posteriorMean e =
      π.blendWeight e * e.strength +
        (1 - π.blendWeight e) * π.mean :=
  BetaPriorMeanConcentration.posteriorMean_eq_blend_empirical_with_prior_mean
    π e hTotal

/-- General Beta posterior concentration is batch/sequential invariant under
PLN count addition. -/
theorem general_beta_posterior_concentration_add_is_sequential
    (π : BetaPriorMeanConcentration) (e₁ e₂ : BinaryCounts) :
    π.posteriorConcentration (e₁.add e₂) =
      (π.posteriorPrior e₁).posteriorConcentration e₂ :=
  BetaPriorMeanConcentration.posteriorConcentration_add_eq_sequential
    π e₁ e₂

/-- General Beta posterior mean is batch/sequential invariant under PLN count
addition: revision adds sufficient statistics, and Bayesian updating can be
performed in either order. -/
theorem general_beta_posterior_mean_add_is_sequential
    (π : BetaPriorMeanConcentration) (e₁ e₂ : BinaryCounts) :
    π.posteriorMean (e₁.add e₂) =
      (π.posteriorPrior e₁).posteriorMean e₂ :=
  BetaPriorMeanConcentration.posteriorMean_add_eq_sequential
    π e₁ e₂

/-- General Beta prior mean is a real strength degree of freedom. -/
theorem general_beta_prior_mean_changes_posterior_strength :
    let e : BinaryCounts :=
      ⟨1, 0, by norm_num, by norm_num⟩
    let π₀ : BetaPriorMeanConcentration :=
      ⟨0, 2, by norm_num, by norm_num, by norm_num⟩
    let π₁ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    π₀.posteriorMean e ≠ π₁.posteriorMean e :=
  BetaPriorMeanConcentration.prior_mean_changes_posterior_strength

/-- General Beta prior concentration is a real confidence/blend-weight degree
of freedom. -/
theorem general_beta_prior_concentration_changes_blend_weight :
    let e : BinaryCounts :=
      ⟨1, 0, by norm_num, by norm_num⟩
    let π₁ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩
    let π₂ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    π₁.blendWeight e ≠ π₂.blendWeight e :=
  BetaPriorMeanConcentration.prior_concentration_changes_blend_weight

/-- Canary: sequential Beta updating agrees with batch evidence revision, while
the prior keeps the posterior mean distinct from the raw empirical strength. -/
theorem general_beta_posterior_mean_sequential_update_canary :
    let π : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    let e₁ : BinaryCounts :=
      ⟨1, 1, by norm_num, by norm_num⟩
    let e₂ : BinaryCounts :=
      ⟨3, 1, by norm_num, by norm_num⟩
    π.posteriorMean (e₁.add e₂) = 5 / 8 ∧
      (π.posteriorPrior e₁).posteriorMean e₂ = 5 / 8 ∧
      π.posteriorMean (e₁.add e₂) ≠ (e₁.add e₂).strength :=
  BetaPriorMeanConcentration.posteriorMean_add_eq_sequential_canary

/-- The multinomial credal-set category envelope agrees with the
`EvidenceDirichlet` IDM formulas. -/
theorem multinomial_credal_envelope_matches_idm_formulas
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
  walleyMultinomial_category_envelope_matches_EvidenceDirichlet ctx e i j hji

/-- For a symmetric Dirichlet prior, the posterior blend weight is exactly the
PLN odds confidence link applied to categorical concentration, with the link
scale set to the prior concentration. -/
theorem symmetric_dirichlet_blend_weight_is_concentration_link
    {k : ℕ} (π : SymmetricDirichletPrior k) (hk : 0 < k)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) :
    π.blendWeight e =
      dirichletPLNConfidenceLink π.priorConcentration
        (by
          have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
          unfold SymmetricDirichletPrior.priorConcentration
          exact mul_pos hkR π.prior_pos)
        (DirichletMeanConcentration.fromCounts e) :=
  SymmetricDirichletPrior.blendWeight_eq_dirichletPLNConfidenceLink
    π hk e

/-- Symmetric Dirichlet posterior means are empirical/prior mean blends, with
blend weight equal to the concentration confidence link. -/
theorem symmetric_dirichlet_posterior_mean_is_concentration_blend
    {k : ℕ} (π : SymmetricDirichletPrior k) (hk : 0 < k)
    (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
    (hTotal : e.total ≠ 0) (i : Fin k) :
    π.posteriorMean e i =
      π.blendWeight e * (DirichletMeanConcentration.fromCounts e).mean i +
        (1 - π.blendWeight e) * π.priorMean :=
  SymmetricDirichletPrior.posteriorMean_eq_blend_empirical_with_prior_mean
    π hk e hTotal i

/-! ## Constructor-profile matrix

The records below are a paper-facing theorem matrix.  Each profile groups the
actual theorem handles that characterize one layer by:

* degrees of freedom / canaries;
* forcing identities;
* invariance laws;
* compatibility boundaries.

Runtime parity is recorded separately as explicit file metadata, because Lean
cannot honestly prove that an external PeTTa or CeTTa command was run.
-/

/-- Audit profile for the confidence portions of the PeTTa truth-function
mirror.  It records the real rule shapes: induction/abduction use weight-space
minimum, revision uses weight addition, negation preserves confidence, and
modus ponens uses a product rule with a concrete canary separating product from
raw minimum. -/
structure PeTTaTruthFunctionAuditProfile where
  inductionConfidenceWeightMin :
    ∀ (a b c ba bc : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction
        a b c ba bc).c =
        Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
          (min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w ba.c)
            (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w bc.c))
  abductionConfidenceWeightMin :
    ∀ (a b c ab cb : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction
        a b c ab cb).c =
        Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
          (min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w ab.c)
            (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w cb.c))
  weightMinCollapsesToMinCappedConfidence :
    ∀ c₁ c₂ : ℝ,
      Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
          (min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w c₁)
            (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w c₂)) =
        min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf c₁)
          (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf c₂)
  revisionConfidenceWeightAddition :
    ∀ (t₁ t₂ : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthRevision t₁ t₂).c =
        min 1 (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
          (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w t₁.c +
            Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w t₂.c))
  negationPreservesConfidence :
    ∀ (t : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthNegation t).c = t.c
  modusPonensConfidenceProduct :
    ∀ (p pq : Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c =
        p.c * pq.c
  modusPonensProductBelowMinCanary :
    (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens
        ⟨0, 0.5⟩ ⟨0, 0.5⟩).c <
      min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf 0.5)
        (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf 0.5)

/-- PeTTa truth-function confidence audit profile. -/
def pettaTruthFunctionAuditProfile : PeTTaTruthFunctionAuditProfile where
  inductionConfidenceWeightMin :=
    petta_induction_confidence_is_weight_min
  abductionConfidenceWeightMin :=
    petta_abduction_confidence_is_weight_min
  weightMinCollapsesToMinCappedConfidence :=
    petta_weight_min_collapses_to_min_capped_confidence
  revisionConfidenceWeightAddition :=
    petta_revision_confidence_is_weight_addition
  negationPreservesConfidence :=
    petta_negation_preserves_confidence
  modusPonensConfidenceProduct :=
    petta_modus_ponens_confidence_is_product
  modusPonensProductBelowMinCanary :=
    petta_modus_ponens_product_below_min_canary

/-- Audit profile for confidence formulas.  It separates bookkeeping unfolds
from actual canaries and forcing laws, so definitional equality does not get
mistaken for semantic corroboration. -/
structure ConfidenceFormulaAuditProfile where
  minConfidenceCorrectIsUnfold :
    ∀ (c₁ c₂ k : ℝ≥0∞),
      let w₁ := c2w c₁ k
      let w₂ := c2w c₂ k
      minConfidenceCorrect c₁ c₂ k = w2c (min w₁ w₂) k
  combineConfidenceCorrectIsUnfold :
    ∀ (tv₁ tv₂ : ProperTruthValue) (k : ℝ≥0∞),
      combineConfidenceCorrect tv₁ tv₂ k =
        w2c (min tv₁.weight tv₂.weight) k
  buggyFormulaCanary :
    combineConfidenceBuggy ⟨0, 1⟩ ⟨0, 1⟩ 1 <
      combineConfidenceCorrect ⟨0, 1⟩ ⟨0, 1⟩ 1
  reconstructionForcesLeftInverse :
    ∀ (encode decode : ℝ → ℝ),
      (∀ {nPlus nMinus : ℝ},
        0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
          (let n := nPlus + nMinus
           let stv : ℝ × ℝ := (nPlus / n, encode n)
           let m := decode stv.2
           (stv.1 * m, (1 - stv.1) * m)) = (nPlus, nMinus)) →
        ∀ {w : ℝ}, 0 < w → decode (encode w) = w
  reconstructionIffLeftInverse :
    ∀ (encode decode : ℝ → ℝ),
      CountReconstruction encode decode ↔ LeftInverseOnPositive encode decode
  leftInverseSufficesForReconstruction :
    ∀ (χ : EvidenceWeightCoordinate) {nPlus nMinus : ℝ},
      0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
        χ.decodeCounts (χ.encodeCounts nPlus nMinus) =
          (nPlus, nMinus)
  plnOddsCoordinateReconstructs :
    ∀ (k : ℝ) (hk : 0 < k) {nPlus nMinus : ℝ},
      0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
        (plnOddsCoordinate k hk).decodeCounts
            ((plnOddsCoordinate k hk).encodeCounts nPlus nMinus) =
          (nPlus, nMinus)
  reserveHalfCoordinateReconstructs :
    ∀ (k : ℝ) (hk : 0 < k) {nPlus nMinus : ℝ},
      0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
        (reserveHalfCoordinate k hk).decodeCounts
            ((reserveHalfCoordinate k hk).encodeCounts nPlus nMinus) =
          (nPlus, nMinus)
  reserveHalfCoordinateFailsWalleyBridge :
    ∀ (s : ℝ) (hs : 0 < s),
      ¬ WidthComplementCompatible (reserveHalfCoordinate s hs) s
  walleyBridgeForcesPLNOdds :
    ∀ (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s),
      WidthComplementCompatible χ s →
        ∀ {n : ℝ}, 0 ≤ n → χ.encode n = (plnOddsCoordinate s hs).encode n
  pettaTruthFunctions : PeTTaTruthFunctionAuditProfile

/-- Confidence formula audit: `_unfold` facts are kept as bookkeeping, while
the real corroborating facts are the buggy-formula canary, reconstruction
necessity, and Walley width-complement forcing. -/
def confidenceFormulaAuditProfile : ConfidenceFormulaAuditProfile where
  minConfidenceCorrectIsUnfold :=
    minConfidenceCorrect_unfold
  combineConfidenceCorrectIsUnfold :=
    combineConfidenceCorrect_unfold
  buggyFormulaCanary :=
    buggy_confidence_formula_underestimates_unit_weight
  reconstructionForcesLeftInverse :=
    reconstructive_confidence_coordinates_need_left_inverse
  reconstructionIffLeftInverse :=
    reconstructive_confidence_coordinates_iff_left_inverse
  leftInverseSufficesForReconstruction :=
    evidence_weight_coordinate_suffices_for_binary_count_reconstruction
  plnOddsCoordinateReconstructs :=
    pln_odds_coordinate_reconstructs_binary_counts
  reserveHalfCoordinateReconstructs :=
    reserve_half_coordinate_reconstructs_binary_counts
  reserveHalfCoordinateFailsWalleyBridge :=
    reconstructive_coordinate_need_not_be_walley_compatible
  walleyBridgeForcesPLNOdds := by
    intro χ s hs hχ n hn
    exact walley_width_complement_forces_pln_odds χ s hs hχ hn
  pettaTruthFunctions :=
    pettaTruthFunctionAuditProfile

/-! ## Confidence revision chart laws -/

/-- Algebraic chart laws for confidence displays under additive evidence-weight
revision.  This profile records the current positive facts, canaries, and the
explicit-gate rigidity theorem for confidence-odds additivity on the
nonnegative evidence-weight axis.  It does not claim that arbitrary
reconstructive confidence charts are PLN. -/
structure ConfidenceRevisionChartProfile where
  confidenceOddsPLNWeight :
    ∀ {k n : ℝ} (hk : 0 < k) (_hn : 0 ≤ n),
      confidenceOdds ((plnOddsCoordinate k hk).encode n) = n / k
  confidenceOddsPLNRevisionAdditive :
    ∀ {k n1 n2 : ℝ} (hk : 0 < k) (_h1 : 0 ≤ n1) (_h2 : 0 ≤ n2),
      confidenceOdds ((plnOddsCoordinate k hk).encode (n1 + n2)) =
        confidenceOdds ((plnOddsCoordinate k hk).encode n1) +
          confidenceOdds ((plnOddsCoordinate k hk).encode n2)
  transportedRevisionOfEncodedWeights :
    ∀ (χ : Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate)
      {w1 w2 : ℝ}, 0 ≤ w1 → 0 ≤ w2 →
        transportedConfidenceRevision χ (χ.encode w1) (χ.encode w2) =
          χ.encode (w1 + w2)
  transportedRevisionAssociativeOnNonnegativeWeights :
    ∀ (χ : Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate)
      {c1 c2 c3 : ℝ},
      0 ≤ χ.decode c1 → 0 ≤ χ.decode c2 → 0 ≤ χ.decode c3 →
        transportedConfidenceRevision χ
            (transportedConfidenceRevision χ c1 c2) c3 =
          transportedConfidenceRevision χ c1
            (transportedConfidenceRevision χ c2 c3)
  walleyWidthComplementEqualsPLNChart :
    ∀ {s n : ℝ} (hs : 0 < s) (_hn : 0 ≤ n),
      1 - walleyPredictiveWidth n s =
        (plnOddsCoordinate s hs).encode n
  walleyWidthComplementConfidenceOdds :
    ∀ {s n : ℝ} (_hs : 0 < s) (_hn : 0 ≤ n),
      confidenceOdds (1 - walleyPredictiveWidth n s) = n / s
  confidenceOddsWeightIdentityForcesPLN :
    ∀ {χ : Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate}
      {k n : ℝ} (hk : 0 < k) (_hn : 0 ≤ n),
      χ.encode n ≠ 1 →
        confidenceOdds (χ.encode n) = n / k →
          χ.encode n = (plnOddsCoordinate k hk).encode n
  canonicalOddsAdditiveForcesPLN :
    ∀ {χ : Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate}
      {k : ℝ} (hk : 0 < k),
      (∀ x y : ℝ,
        0 ≤ x → 0 ≤ y →
        confidenceOdds (χ.encode (x + y)) =
          confidenceOdds (χ.encode x) + confidenceOdds (χ.encode y)) →
      ContinuousOn
        (fun w : ℝ => confidenceOdds (χ.encode w)) (Set.Ici (0 : ℝ)) →
      confidenceOdds (χ.encode 1) = 1 / k →
      (∀ {n : ℝ}, 0 ≤ n → χ.encode n ≠ 1) →
      ∀ {n : ℝ}, 0 ≤ n →
        χ.encode n = (plnOddsCoordinate k hk).encode n
  canonicalOddsMonotoneAdditiveForcesPLN :
    ∀ {χ : Mettapedia.Logic.PLNConfidenceWeight.EvidenceWeightCoordinate}
      {k : ℝ} (hk : 0 < k),
      (∀ x y : ℝ,
        0 ≤ x → 0 ≤ y →
        confidenceOdds (χ.encode (x + y)) =
          confidenceOdds (χ.encode x) + confidenceOdds (χ.encode y)) →
      MonotoneOn
        (fun w : ℝ => confidenceOdds (χ.encode w)) (Set.Ici (0 : ℝ)) →
      confidenceOdds (χ.encode 1) = 1 / k →
      (∀ {n : ℝ}, 0 ≤ n → χ.encode n ≠ 1) →
      ∀ {n : ℝ}, 0 ≤ n →
        χ.encode n = (plnOddsCoordinate k hk).encode n
  plnOddsCoordinateSatisfiesCanonicalGates :
    ∀ {k : ℝ} (hk : 0 < k),
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        confidenceOdds ((plnOddsCoordinate k hk).encode (x + y)) =
          confidenceOdds ((plnOddsCoordinate k hk).encode x) +
            confidenceOdds ((plnOddsCoordinate k hk).encode y)) ∧
      ContinuousOn
        (fun w : ℝ => confidenceOdds ((plnOddsCoordinate k hk).encode w))
        (Set.Ici (0 : ℝ)) ∧
      confidenceOdds ((plnOddsCoordinate k hk).encode 1) = 1 / k ∧
      (∀ {n : ℝ}, 0 ≤ n → (plnOddsCoordinate k hk).encode n ≠ 1)
  plnOddsCoordinateSatisfiesMonotoneCanonicalGates :
    ∀ {k : ℝ} (hk : 0 < k),
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        confidenceOdds ((plnOddsCoordinate k hk).encode (x + y)) =
          confidenceOdds ((plnOddsCoordinate k hk).encode x) +
            confidenceOdds ((plnOddsCoordinate k hk).encode y)) ∧
      MonotoneOn
        (fun w : ℝ => confidenceOdds ((plnOddsCoordinate k hk).encode w))
        (Set.Ici (0 : ℝ)) ∧
      confidenceOdds ((plnOddsCoordinate k hk).encode 1) = 1 / k ∧
      (∀ {n : ℝ}, 0 ≤ n → (plnOddsCoordinate k hk).encode n ≠ 1)
  plnRevisionClosedForm :
    ∀ {k n1 n2 : ℝ} (hk : 0 < k) (_h1 : 0 ≤ n1) (_h2 : 0 ≤ n2),
      (plnOddsCoordinate k hk).encode (n1 + n2) =
        plnConfidenceRevision
          ((plnOddsCoordinate k hk).encode n1)
          ((plnOddsCoordinate k hk).encode n2)
  expCoordinateReconstructs :
    ∀ (k : ℝ) (hk : 0 < k) {w : ℝ}, 0 ≤ w →
      (expCoordinate k hk).decode ((expCoordinate k hk).encode w) = w
  expRevisionClosedForm :
    ∀ {k n1 n2 : ℝ} (hk : 0 < k),
      (expCoordinate k hk).encode (n1 + n2) =
        expConfidenceRevision ((expCoordinate k hk).encode n1)
          ((expCoordinate k hk).encode n2)
  tanhCoordinateReconstructs :
    ∀ (k : ℝ) (hk : 0 < k) {w : ℝ}, 0 ≤ w →
      (tanhCoordinate k hk).decode ((tanhCoordinate k hk).encode w) = w
  tanhRevisionClosedForm :
    ∀ {k n1 n2 : ℝ} (hk : 0 < k),
      (tanhCoordinate k hk).encode (n1 + n2) =
        tanhConfidenceRevision ((tanhCoordinate k hk).encode n1)
          ((tanhCoordinate k hk).encode n2)
  arctanCoordinateReconstructs :
    ∀ (k : ℝ) (hk : 0 < k) {w : ℝ}, 0 ≤ w →
      (arctanCoordinate k hk).decode ((arctanCoordinate k hk).encode w) = w
  expRevisionDiffersFromPLN :
    expConfidenceRevision (1 / 2) (1 / 2) ≠
      plnConfidenceRevision (1 / 2) (1 / 2)
  plnRevisionConfidenceOddsAdditiveAtHalf :
    confidenceOdds (plnConfidenceRevision (1 / 2) (1 / 2)) =
      confidenceOdds (1 / 2) + confidenceOdds (1 / 2)
  expRevisionNotConfidenceOddsAdditiveAtHalf :
    confidenceOdds (expConfidenceRevision (1 / 2) (1 / 2)) ≠
      confidenceOdds (1 / 2) + confidenceOdds (1 / 2)
  tanhRevisionDiffersFromPLN :
    tanhConfidenceRevision (1 / 2) (1 / 2) ≠
      plnConfidenceRevision (1 / 2) (1 / 2)

/-- Current confidence-revision chart package.  PLN has additive confidence
odds and the Mobius transported law; exponential has the noisy-OR transported
law; tanh has the Einstein-style transported law; arctan is a reconstructive
non-Mobius chart.  Rigidity is included only under the explicit additive,
continuous or monotone, normalized, nonsingular confidence-odds hypotheses on
the nonnegative evidence-weight axis, together with PLN non-vacuity witnesses. -/
noncomputable def confidenceRevisionChartProfile : ConfidenceRevisionChartProfile where
  confidenceOddsPLNWeight := by
    intro k n hk hn
    exact confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk hn
  confidenceOddsPLNRevisionAdditive := by
    intro k n1 n2 hk h1 h2
    exact confidenceOdds_pln_revision_additive hk h1 h2
  transportedRevisionOfEncodedWeights := by
    intro χ w1 w2 h1 h2
    exact transportedConfidenceRevision_of_encoded_weights χ h1 h2
  transportedRevisionAssociativeOnNonnegativeWeights := by
    intro χ c1 c2 c3 h1 h2 h3
    exact transportedConfidenceRevision_assoc_of_nonneg χ h1 h2 h3
  walleyWidthComplementEqualsPLNChart := by
    intro s n hs hn
    exact walley_width_complement_eq_plnOddsCoordinate_encode hs hn
  walleyWidthComplementConfidenceOdds := by
    intro s n hs hn
    exact confidenceOdds_walley_width_complement_eq_weight_div hs hn
  confidenceOddsWeightIdentityForcesPLN := by
    intro χ k n hk hn hnot hχ
    exact confidenceOdds_weight_identity_forces_pln_encode hk hn hnot hχ
  canonicalOddsAdditiveForcesPLN := by
    intro χ k hk hadd hcont hnorm hnot n hn
    exact canonical_odds_additive_forces_pln hk hadd hcont hnorm hnot hn
  canonicalOddsMonotoneAdditiveForcesPLN := by
    intro χ k hk hadd hmono hnorm hnot n hn
    exact canonical_odds_monotone_additive_forces_pln hk hadd hmono hnorm hnot hn
  plnOddsCoordinateSatisfiesCanonicalGates := by
    intro k hk
    exact plnOddsCoordinate_satisfies_canonical_gates hk
  plnOddsCoordinateSatisfiesMonotoneCanonicalGates := by
    intro k hk
    exact plnOddsCoordinate_satisfies_monotone_canonical_gates hk
  plnRevisionClosedForm := by
    intro k n1 n2 hk h1 h2
    exact plnConfidence_revision_closedForm hk h1 h2
  expCoordinateReconstructs := by
    intro k hk w hw
    exact expCoordinate_decode_encode k hk hw
  expRevisionClosedForm := by
    intro k n1 n2 hk
    exact expCoordinate_revision_closedForm hk
  tanhCoordinateReconstructs := by
    intro k hk w hw
    exact tanhCoordinate_decode_encode k hk hw
  tanhRevisionClosedForm := by
    intro k n1 n2 hk
    exact tanhCoordinate_revision_closedForm hk
  arctanCoordinateReconstructs := by
    intro k hk w hw
    exact arctanCoordinate_decode_encode k hk hw
  expRevisionDiffersFromPLN :=
    expRevision_differs_from_plnRevision_at_half
  plnRevisionConfidenceOddsAdditiveAtHalf :=
    plnRevision_confidenceOdds_additive_at_half
  expRevisionNotConfidenceOddsAdditiveAtHalf :=
    expRevision_not_confidenceOdds_additive_at_half
  tanhRevisionDiffersFromPLN :=
    tanhRevision_differs_from_plnRevision_at_half

/-- Abstract torsor profile for fully lossless confidence charts with a fixed
display type.  This deliberately uses the stronger equivalence-based chart
type rather than the weaker `EvidenceWeightCoordinate`, whose contract is only
left-inverse reconstruction on nonnegative weights. -/
structure ConfidenceChartTorsorProfile where
  chartDifferenceTransitive :
    ∀ {Display : Type} (χ ψ : EvidenceWeightChartIso Display),
      reparametrizeChart (chartDifference χ ψ) χ = ψ
  chartActionFree :
    ∀ {Display : Type} (χ : EvidenceWeightChartIso Display)
      {σ τ : Equiv.Perm Display},
      reparametrizeChart σ χ = reparametrizeChart τ χ → σ = τ
  chartDifferenceUnique :
    ∀ {Display : Type} (χ ψ : EvidenceWeightChartIso Display)
      (σ : Equiv.Perm Display),
      reparametrizeChart σ χ = ψ ↔ σ = chartDifference χ ψ
  chartSelfDifferenceIdentity :
    ∀ {Display : Type} (χ : EvidenceWeightChartIso Display),
      chartDifference χ χ = Equiv.refl Display
  orderedChartDifferenceTransitive :
    ∀ {Display : Type} [LE Display]
      (χ ψ : OrderedEvidenceWeightChartIso Display),
      reparametrizeOrderedChart (orderedChartDifference χ ψ) χ = ψ
  orderedChartActionFree :
    ∀ {Display : Type} [LE Display]
      (χ : OrderedEvidenceWeightChartIso Display)
      {σ τ : Display ≃o Display},
      reparametrizeOrderedChart σ χ = reparametrizeOrderedChart τ χ → σ = τ
  orderedChartDifferenceUnique :
    ∀ {Display : Type} [LE Display]
      (χ ψ : OrderedEvidenceWeightChartIso Display)
      (σ : Display ≃o Display),
      reparametrizeOrderedChart σ χ = ψ ↔ σ = orderedChartDifference χ ψ
  orderedChartSelfDifferenceIdentity :
    ∀ {Display : Type} [LE Display]
      (χ : OrderedEvidenceWeightChartIso Display),
      orderedChartDifference χ χ = OrderIso.refl Display
  orderedChartActionForgetsToEquivAction :
    ∀ {Display : Type} [LE Display]
      (σ : Display ≃o Display) (χ : OrderedEvidenceWeightChartIso Display),
      (reparametrizeOrderedChart σ χ).toChartIso =
        reparametrizeChart σ.toEquiv χ.toChartIso
  orderedChartDifferenceForgetsToEquivDifference :
    ∀ {Display : Type} [LE Display]
      (χ ψ : OrderedEvidenceWeightChartIso Display),
      (orderedChartDifference χ ψ).toEquiv =
        chartDifference χ.toChartIso ψ.toChartIso
  rawPermutationNeedNotBeMonotone :
    ¬ Monotone (Equiv.swap false true : Equiv.Perm Bool)

/-- Fully lossless confidence charts form a torsor under display-space
reparametrizations: differences between charts are canonical, but no chart is
distinguished without an extra law such as Walley width complement or
canonical confidence-odds additivity. -/
noncomputable def confidenceChartTorsorProfile : ConfidenceChartTorsorProfile where
  chartDifferenceTransitive :=
    reparametrizeChart_chartDifference
  chartActionFree :=
    reparametrizeChart_free
  chartDifferenceUnique :=
    chartDifference_unique
  chartSelfDifferenceIdentity :=
    chartDifference_self
  orderedChartDifferenceTransitive :=
    reparametrizeOrderedChart_orderedChartDifference
  orderedChartActionFree :=
    reparametrizeOrderedChart_free
  orderedChartDifferenceUnique :=
    orderedChartDifference_unique
  orderedChartSelfDifferenceIdentity :=
    orderedChartDifference_self
  orderedChartActionForgetsToEquivAction :=
    reparametrizeOrderedChart_toChartIso
  orderedChartDifferenceForgetsToEquivDifference :=
    orderedChartDifference_toEquiv
  rawPermutationNeedNotBeMonotone :=
    boolSwap_not_monotone

/-- Generic ITVs expose the ambient degrees of freedom: width, credibility,
and point-projection selector are not mutually forced. -/
structure GenericITVProfile where
  widthDoesNotForceCredibility :
    ∃ itv₀ itv₁ : ITV,
      itv₀.width = itv₁.width ∧ itv₀.credibility ≠ itv₁.credibility
  credibilityDoesNotForceWidth :
    ∃ itv₀ itv₁ : ITV,
      itv₀.credibility = itv₁.credibility ∧ itv₀.width ≠ itv₁.width
  pointProjectionNotForced :
    ∃ itv : ITV,
      Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ∧
        Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv ∧
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
            Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv

/-- The generic ITV profile is fully witnessed by explicit canaries. -/
def genericITVProfile : GenericITVProfile where
  widthDoesNotForceCredibility :=
    generic_itv_width_does_not_force_credibility
  credibilityDoesNotForceWidth :=
    generic_itv_credibility_does_not_force_width
  pointProjectionNotForced :=
    generic_itv_does_not_force_point_projection

/-- Strength projection profile: a generic interval does not choose one point
projection, while the current midpoint view is an ordered, unit-bounded
projection of any typed ITV and an average of the forced envelope in the credal
projection tower. -/
structure StrengthProjectionProfile where
  lowerMidpointUpperNotForced :
    ∃ itv : ITV,
      Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ∧
        Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv ∧
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
            Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv
  typedITVLowerLeMidpoint :
    ∀ {Sem : Mettapedia.Logic.PLNTruthTower.ITVSemantics.{0}}
      (x : Mettapedia.Logic.PLNTruthTower.TypedITV Sem),
      x.lower ≤ x.midpoint
  typedITVMidpointLeUpper :
    ∀ {Sem : Mettapedia.Logic.PLNTruthTower.ITVSemantics.{0}}
      (x : Mettapedia.Logic.PLNTruthTower.TypedITV Sem),
      x.midpoint ≤ x.upper
  typedITVMidpointInUnit :
    ∀ {Sem : Mettapedia.Logic.PLNTruthTower.ITVSemantics.{0}}
      (x : Mettapedia.Logic.PLNTruthTower.TypedITV Sem),
      x.midpoint ∈ Set.Icc (0 : ℝ) 1
  credalTowerMidpointAverage :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω),
      t.midpointDisplay =
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            t.credal t.gamble +
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            t.credal t.gamble) / 2
  credalTowerLowerLeMidpoint :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω),
      t.toTypedITV.lower ≤ t.midpointDisplay
  credalTowerMidpointLeUpper :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω),
      t.midpointDisplay ≤ t.toTypedITV.upper
  typedSTVSameStrengthDifferentConfidence :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 2 2)
    x.strength = y.strength ∧ x.confidence.display ≠ y.confidence.display
  typedSTVSameConfidenceDifferentStrength :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 2 0)
    x.confidence.display = y.confidence.display ∧ x.strength ≠ y.strength
  improperPosteriorIsMLE :
    ∀ (e : Mettapedia.Logic.PLNTruthTower.BinaryCounts),
      Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.improper e =
        e.mleStrength
  posteriorMeanInUnit :
    ∀ (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
      (e : Mettapedia.Logic.PLNTruthTower.BinaryCounts),
      0 <
          Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorDenom ctx e →
        0 ≤
            Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength ctx e ∧
          Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength ctx e ≤ 1
  priorChoiceCanChangeDisplayedStrength :
    Mettapedia.Logic.PLNTruthTower.BinaryCounts.singlePositive.mleStrength = 1 ∧
      Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
          Mettapedia.Logic.PLNTruthTower.BinaryCounts.singlePositive =
        (2 / 3 : ℝ) ∧
        Mettapedia.Logic.PLNTruthTower.BinaryCounts.singlePositive.mleStrength ≠
          Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
            Mettapedia.Logic.PLNTruthTower.BinaryCounts.singlePositive
  natMleIsHaldane :
    ∀ (nPos nNeg : ℕ),
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength =
        Mettapedia.Logic.EvidenceBeta.predHaldane nPos nNeg
  natUniformIsLaplace :
    ∀ (nPos nNeg : ℕ),
      Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
          (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg) =
        Mettapedia.Logic.EvidenceBeta.predLaplace nPos nNeg
  natJeffreysIsKT :
    ∀ (nPos nNeg : ℕ),
      Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
          (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg) =
        Mettapedia.Logic.EvidenceBeta.predJeffreys nPos nNeg
  natPriorMatters :
    (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 0 1).mleStrength = 0 ∧
      Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
          Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
          (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 0 1) =
        (1 / 4 : ℝ) ∧
        Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
            (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 0 1) =
          (1 / 3 : ℝ)
  laplaceDifferenceBound :
    ∀ (nPos nNeg : ℕ), nPos + nNeg ≠ 0 →
      |(Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength -
          Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.Logic.EvidenceClass.BinaryContext.uniform
            (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg)| ≤
        2 / ((nPos : ℝ) + (nNeg : ℝ) + 2)
  jeffreysDifferenceBound :
    ∀ (nPos nNeg : ℕ), nPos + nNeg ≠ 0 →
      |(Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength -
          Mettapedia.Logic.PLNTruthTower.BinaryCounts.posteriorMeanStrength
            Mettapedia.Logic.EvidenceClass.BinaryContext.jeffreys
            (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg)| ≤
        1 / (2 * ((nPos : ℝ) + (nNeg : ℝ) + 1))
  symmetricPriorConvergence :
    ∀ ε : ℝ, 0 < ε → ∀ priorParam : ℝ, 0 < priorParam →
      ∃ N : ℕ, ∀ nPos nNeg : ℕ, nPos + nNeg ≥ N → nPos + nNeg ≠ 0 →
        let strength :=
          (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts nPos nNeg).mleStrength
        let mean :=
          ((nPos : ℝ) + priorParam) /
            ((nPos : ℝ) + (nNeg : ℝ) + 2 * priorParam)
        |strength - mean| < ε

/-- Current strength projection profile. -/
def strengthProjectionProfile : StrengthProjectionProfile where
  lowerMidpointUpperNotForced :=
    generic_itv_does_not_force_point_projection
  typedITVLowerLeMidpoint :=
    typed_itv_lower_le_midpoint
  typedITVMidpointLeUpper :=
    typed_itv_midpoint_le_upper
  typedITVMidpointInUnit :=
    typed_itv_midpoint_in_unit
  credalTowerMidpointAverage :=
    credal_projection_tower_midpoint_is_envelope_average
  credalTowerLowerLeMidpoint :=
    credal_projection_tower_lower_le_midpoint
  credalTowerMidpointLeUpper :=
    credal_projection_tower_midpoint_le_upper
  typedSTVSameStrengthDifferentConfidence :=
    typed_stv_same_strength_can_have_different_confidence
  typedSTVSameConfidenceDifferentStrength :=
    typed_stv_same_confidence_can_have_different_strength
  improperPosteriorIsMLE :=
    binary_counts_improper_posterior_strength_eq_mle
  posteriorMeanInUnit :=
    binary_counts_posterior_mean_strength_in_unit
  priorChoiceCanChangeDisplayedStrength :=
    binary_counts_uniform_prior_changes_displayed_strength
  natMleIsHaldane :=
    binary_counts_of_nat_mle_eq_haldane
  natUniformIsLaplace :=
    binary_counts_of_nat_uniform_eq_laplace
  natJeffreysIsKT :=
    binary_counts_of_nat_jeffreys_eq_kt
  natPriorMatters :=
    binary_counts_of_nat_prior_matters_example
  laplaceDifferenceBound :=
    binary_counts_haldane_vs_laplace_difference
  jeffreysDifferenceBound :=
    binary_counts_haldane_vs_jeffreys_difference
  symmetricPriorConvergence :=
    binary_counts_mle_converges_to_symmetric_posterior_mean

/-- Bayesian credible ITVs fix the credibility coordinate from evidence
concentration while leaving interval construction to backend/level choices. -/
structure BayesCredibleProfile where
  credibilityConcentration :
    ∀ (backend : Mettapedia.Logic.EvidenceBeta.CredibleIntervalBackend)
      (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
      (level : ℝ) (hlevel : 0 < level ∧ level < 1)
      (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence),
      (TypedITV.fromBayesCredible backend ctx level hlevel e).credibility =
        (Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toConfidence
          (ctx.α₀ + ctx.β₀) e).toReal
  credibilityIndependentOfBackendLevel :
    ∀ (backend₁ backend₂ :
        Mettapedia.Logic.EvidenceBeta.CredibleIntervalBackend)
      (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
      (ctx : Mettapedia.Logic.EvidenceClass.BinaryContext)
      (level₁ level₂ : ℝ)
      (hlevel₁ : 0 < level₁ ∧ level₁ < 1)
      (hlevel₂ : 0 < level₂ ∧ level₂ < 1),
      (ITV.fromBayesCredibleWithBackend backend₁ e ctx level₁ hlevel₁).credibility =
        (ITV.fromBayesCredibleWithBackend backend₂ e ctx level₂ hlevel₂).credibility

/-- Bayesian credible profile: evidence concentration forces credibility, not
the interval backend. -/
def bayesCredibleProfile : BayesCredibleProfile where
  credibilityConcentration :=
    typed_bayes_credible_credibility_is_evidence_concentration
  credibilityIndependentOfBackendLevel :=
    ITV.fromBayesCredibleWithBackend_credibility_independent_of_backend_level

/-- Walley binary IDM narrows the confidence coordinate by the
width-complement bridge. -/
structure WalleyBinaryProfile where
  typedWidthComplement :
    ∀ (s : ℝ) (hs : 0 < s)
      (e : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence),
      (TypedITV.fromWalleyBinary s hs e).width +
        (TypedITV.fromWalleyBinary s hs e).credibility = 1
  widthComplementForcesPLNOdds :
    ∀ (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s),
      WidthComplementCompatible χ s →
        ∀ {n : ℝ}, 0 ≤ n → χ.encode n = (plnOddsCoordinate s hs).encode n
  reconstructiveNonWalleyCanary :
    ∀ (s : ℝ) (hs : 0 < s),
      ¬ WidthComplementCompatible (reserveHalfCoordinate s hs) s

/-- Walley binary profile: generic reconstructivity is not enough; the
width-complement law is the forcing hypothesis. -/
def walleyBinaryProfile : WalleyBinaryProfile where
  typedWidthComplement :=
    typed_walley_binary_has_width_complement
  widthComplementForcesPLNOdds := by
    intro χ s hs hχ n hn
    exact walley_width_complement_forces_pln_odds χ s hs hχ hn
  reconstructiveNonWalleyCanary :=
    reconstructive_coordinate_need_not_be_walley_compatible

/-- Walley categorical IDM is the multinomial counterpart: category envelopes
come from the credal set and carry the same width-complement precision law. -/
structure WalleyCategoricalProfile where
  typedWidthComplement :
    ∀ {k : ℕ}
      (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
      (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k),
      (TypedITV.fromWalleyCategorical ctx e i).width +
        (TypedITV.fromWalleyCategorical ctx e i).credibility = 1
  typedCredibilityPrecision :
    ∀ {k : ℕ}
      (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
      (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k) (i : Fin k),
      (TypedITV.fromWalleyCategorical ctx e i).credibility =
        (e.total : ℝ) / Mettapedia.Logic.EvidenceDirichlet.idmDenom ctx e
  widthMatchesCredalEnvelope :
    ∀ {k : ℕ}
      (ctx : Mettapedia.Logic.EvidenceDirichlet.IDMPredictiveContext)
      (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k)
      (i j : Fin k) (_ : j ≠ i),
      (TypedITV.fromWalleyCategorical ctx e i).width =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
            (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i) -
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (Mettapedia.Logic.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
            (Mettapedia.Logic.WalleyMultinomialIDM.categoryGamble i)

/-- Walley categorical profile: multinomial IDM as typed ITV plus credal
envelope agreement. -/
def walleyCategoricalProfile : WalleyCategoricalProfile where
  typedWidthComplement :=
    typed_walley_categorical_has_width_complement
  typedCredibilityPrecision :=
    typed_walley_categorical_credibility_is_idm_precision
  widthMatchesCredalEnvelope :=
    typed_walley_categorical_width_matches_credal_envelope

/-- Mean/concentration coordinates are lossless evidence coordinates, but do
not choose a confidence link by themselves. -/
structure MeanConcentrationProfile where
  binaryPolarEquiv :
    {e : BinaryCounts // 0 < e.total} ≃ BinarySimplexScale
  binaryPolarToCountsTotal :
    ∀ z : BinarySimplexScale,
      (binarySimplexScaleToCounts z).total = z.total
  binaryPolarToCountsStrength :
    ∀ z : BinarySimplexScale,
      (binarySimplexScaleToCounts z).strength = z.strength
  binaryAddStrengthWeightedMixture :
    ∀ (e₁ e₂ : BinaryCounts),
      e₁.total ≠ 0 → e₂.total ≠ 0 → e₁.total + e₂.total ≠ 0 →
        (e₁.add e₂).strength =
          (e₁.strength * e₁.total + e₂.strength * e₂.total) /
            (e₁.total + e₂.total)
  binaryTypedRevisionStrengthWeightedMixture :
    ∀ (χ : EvidenceWeightCoordinate) (e₁ e₂ : BinaryCounts),
      (TypedSTV.revise (TypedSTV.fromCounts χ e₁)
        (TypedSTV.fromCounts χ e₂)).strength =
          (e₁.strength * e₁.total + e₂.strength * e₂.total) /
            (e₁.total + e₂.total)
  binaryLossless :
    ∀ (e : BinaryCounts), e.total ≠ 0 →
      (BetaMeanConcentration.fromCounts e).decodeCounts =
        (e.nPlus, e.nMinus)
  binaryTypedSTVFactorsThroughMeanConcentration :
    ∀ (χ : EvidenceWeightCoordinate) (e : BinaryCounts),
      (BetaMeanConcentration.fromCounts e).toTypedSTV χ =
        TypedSTV.fromCounts χ e
  categoricalLossless :
    ∀ {k : ℕ}
      (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k),
      e.total ≠ 0 → ∀ i : Fin k,
        (DirichletMeanConcentration.fromCounts e).decodeCounts i =
          (e.counts i : ℝ)
  categoricalTypedTruthFactorsThroughMeanConcentration :
    ∀ {k : ℕ} (χ : EvidenceWeightCoordinate)
      (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k),
      (DirichletMeanConcentration.fromCounts e).toTypedTruth χ =
        TypedCategoricalTruth.fromCounts χ e
  binaryLinkNotForced :
    let z : BetaMeanConcentration := ⟨1 / 2, 1⟩
    plnConfidenceLink 1 (by norm_num) z ≠
      reserveHalfLink 1 (by norm_num) z
  binaryBlendWeightIsConcentrationLink :
    ∀ (π : SymmetricBetaPrior) (e : BinaryCounts),
      π.blendWeight e =
        plnConfidenceLink (2 * π.prior) (by nlinarith [π.prior_pos])
          (BetaMeanConcentration.fromCounts e)
  binaryGeneralBetaBlendWeightIsConcentrationLink :
    ∀ (π : BetaPriorMeanConcentration) (e : BinaryCounts),
      π.blendWeight e =
        plnConfidenceLink π.concentration π.concentration_pos
          (BetaMeanConcentration.fromCounts e)
  binaryPosteriorMeanBlend :
    ∀ (π : SymmetricBetaPrior) (e : BinaryCounts),
      e.total ≠ 0 →
        π.posteriorMean e =
          π.blendWeight e * e.strength +
            (1 - π.blendWeight e) * (1 / 2 : ℝ)
  binaryGeneralBetaPosteriorMeanBlend :
    ∀ (π : BetaPriorMeanConcentration) (e : BinaryCounts),
      e.total ≠ 0 →
        π.posteriorMean e =
          π.blendWeight e * e.strength +
            (1 - π.blendWeight e) * π.mean
  binaryGeneralBetaPosteriorConcentrationSequential :
    ∀ (π : BetaPriorMeanConcentration) (e₁ e₂ : BinaryCounts),
      π.posteriorConcentration (e₁.add e₂) =
        (π.posteriorPrior e₁).posteriorConcentration e₂
  binaryGeneralBetaPosteriorMeanSequential :
    ∀ (π : BetaPriorMeanConcentration) (e₁ e₂ : BinaryCounts),
      π.posteriorMean (e₁.add e₂) =
        (π.posteriorPrior e₁).posteriorMean e₂
  binaryPriorMeanChangesPosteriorStrength :
    let e : BinaryCounts :=
      ⟨1, 0, by norm_num, by norm_num⟩
    let π₀ : BetaPriorMeanConcentration :=
      ⟨0, 2, by norm_num, by norm_num, by norm_num⟩
    let π₁ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    π₀.posteriorMean e ≠ π₁.posteriorMean e
  binaryPriorConcentrationChangesBlendWeight :
    let e : BinaryCounts :=
      ⟨1, 0, by norm_num, by norm_num⟩
    let π₁ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩
    let π₂ : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    π₁.blendWeight e ≠ π₂.blendWeight e
  binaryPosteriorMeanSequentialUpdateCanary :
    let π : BetaPriorMeanConcentration :=
      ⟨1 / 2, 2, by norm_num, by norm_num, by norm_num⟩
    let e₁ : BinaryCounts :=
      ⟨1, 1, by norm_num, by norm_num⟩
    let e₂ : BinaryCounts :=
      ⟨3, 1, by norm_num, by norm_num⟩
    π.posteriorMean (e₁.add e₂) = 5 / 8 ∧
      (π.posteriorPrior e₁).posteriorMean e₂ = 5 / 8 ∧
      π.posteriorMean (e₁.add e₂) ≠ (e₁.add e₂).strength
  categoricalLinkNotForced :
    let z : DirichletMeanConcentration 3 := ⟨fun _ => 1 / 3, 1⟩
    dirichletPLNConfidenceLink 1 (by norm_num) z ≠
      dirichletReserveHalfLink 1 (by norm_num) z
  categoricalBlendWeightIsConcentrationLink :
    ∀ {k : ℕ} (π : SymmetricDirichletPrior k) (hk : 0 < k)
      (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k),
      π.blendWeight e =
        dirichletPLNConfidenceLink π.priorConcentration
          (by
            have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
            unfold SymmetricDirichletPrior.priorConcentration
            exact mul_pos hkR π.prior_pos)
          (DirichletMeanConcentration.fromCounts e)
  categoricalPosteriorMeanBlend :
    ∀ {k : ℕ} (π : SymmetricDirichletPrior k) (_ : 0 < k)
      (e : Mettapedia.Logic.EvidenceDirichlet.MultiEvidence k),
      e.total ≠ 0 → ∀ i : Fin k,
        π.posteriorMean e i =
          π.blendWeight e * (DirichletMeanConcentration.fromCounts e).mean i +
            (1 - π.blendWeight e) * π.priorMean

/-- Mean/concentration profile: evidence coordinates are lossless, confidence
display is a separate link choice; under symmetric conjugate priors, the PLN
concentration link is exactly the posterior empirical/prior blend weight. -/
noncomputable def meanConcentrationProfile : MeanConcentrationProfile where
  binaryPolarEquiv :=
    positiveBinaryCountsEquivSimplexScale
  binaryPolarToCountsTotal :=
    binarySimplexScaleToCounts_total
  binaryPolarToCountsStrength :=
    binarySimplexScaleToCounts_strength
  binaryAddStrengthWeightedMixture :=
    BinaryCounts.add_strength_eq_weighted_mixture
  binaryTypedRevisionStrengthWeightedMixture :=
    typedSTV_revision_fromCounts_strength_eq_weighted_mixture
  binaryLossless :=
    binary_mean_concentration_is_lossless
  binaryTypedSTVFactorsThroughMeanConcentration :=
    BetaMeanConcentration.typedSTV_fromCounts_factors_through_betaCoordinate
  categoricalLossless := by
    intro k e hTotal i
    exact categorical_mean_concentration_is_lossless e hTotal i
  categoricalTypedTruthFactorsThroughMeanConcentration := by
    intro k χ e
    exact
      DirichletMeanConcentration.typedCategorical_fromCounts_factors_through_dirichletCoordinate
        χ e
  binaryLinkNotForced :=
    beta_coordinate_does_not_force_confidence_link
  binaryBlendWeightIsConcentrationLink :=
    symmetric_beta_blend_weight_is_concentration_link
  binaryGeneralBetaBlendWeightIsConcentrationLink :=
    general_beta_blend_weight_is_concentration_link
  binaryPosteriorMeanBlend :=
    symmetric_beta_posterior_mean_is_concentration_blend
  binaryGeneralBetaPosteriorMeanBlend :=
    general_beta_posterior_mean_is_concentration_blend
  binaryGeneralBetaPosteriorConcentrationSequential :=
    general_beta_posterior_concentration_add_is_sequential
  binaryGeneralBetaPosteriorMeanSequential :=
    general_beta_posterior_mean_add_is_sequential
  binaryPriorMeanChangesPosteriorStrength :=
    general_beta_prior_mean_changes_posterior_strength
  binaryPriorConcentrationChangesBlendWeight :=
    general_beta_prior_concentration_changes_blend_weight
  binaryPosteriorMeanSequentialUpdateCanary :=
    general_beta_posterior_mean_sequential_update_canary
  categoricalLinkNotForced :=
    dirichlet_coordinate_does_not_force_confidence_link
  categoricalBlendWeightIsConcentrationLink :=
    symmetric_dirichlet_blend_weight_is_concentration_link
  categoricalPosteriorMeanBlend := by
    intro k π hk e hTotal i
    exact symmetric_dirichlet_posterior_mean_is_concentration_blend
      π hk e hTotal i

/-- Information-geometric lift profile for the finite Bernoulli/Beta slice:
strength is the mean/m-coordinate, log support-odds is the natural/e-coordinate,
and concentration is the separate evidence-weight axis on which confidence
links live. -/
structure InformationGeometryLiftProfile where
  naturalToMeanPositive :
    ∀ θ : ℝ, 0 < bernoulliNaturalToMean θ
  naturalToMeanLtOne :
    ∀ θ : ℝ, bernoulliNaturalToMean θ < 1
  logOddsNaturalToMean :
    ∀ θ : ℝ, bernoulliLogOdds (bernoulliNaturalToMean θ) = θ
  naturalToMeanLogOdds :
    ∀ {p : ℝ}, 0 < p → p < 1 →
      bernoulliNaturalToMean (bernoulliLogOdds p) = p
  hellingerUnitCircle :
    ∀ {p : ℝ}, 0 ≤ p → p ≤ 1 →
      (bernoulliHellingerEmbedding p).1 ^ 2 +
          (bernoulliHellingerEmbedding p).2 ^ 2 = 1
  fisherMetricPositive :
    ∀ {p : ℝ}, 0 < p → p < 1 → 0 < bernoulliFisherMetric p
  fisherMetricHalf :
    bernoulliFisherMetric (1 / 2) = 4
  fisherTensorSymmetric :
    ∀ p v w : ℝ, bernoulliFisherTensor p v w = bernoulliFisherTensor p w v
  fisherTensorDiagPositive :
    ∀ {p v : ℝ}, 0 < p → p < 1 → v ≠ 0 →
      0 < bernoulliFisherTensor p v v
  fisherTensorHalf :
    ∀ v w : ℝ, bernoulliFisherTensor (1 / 2) v w = 4 * v * w
  mixtureGeodesicOpen :
    ∀ {p q t : ℝ}, 0 < p → p < 1 → 0 < q → q < 1 → 0 < t → t < 1 →
      0 < bernoulliMixtureGeodesic p q t ∧
        bernoulliMixtureGeodesic p q t < 1
  exponentialGeodesicOpen :
    ∀ p q t : ℝ,
      0 < bernoulliExponentialGeodesic p q t ∧
        bernoulliExponentialGeodesic p q t < 1
  exponentialGeodesicNaturalLinear :
    ∀ p q t : ℝ,
      bernoulliLogOdds (bernoulliExponentialGeodesic p q t) =
        (1 - t) * bernoulliLogOdds p + t * bernoulliLogOdds q
  mixtureGeodesicVelocityPathAgrees :
    ∀ p q t : ℝ,
      bernoulliMixtureGeodesicVelocityPath p q t =
        bernoulliMixtureGeodesic p q t
  mixtureGeodesicConstantVelocity :
    ∀ p q t : ℝ,
      HasDerivAt (fun τ : ℝ => bernoulliMixtureGeodesic p q τ)
        (q - p) t
  exponentialGeodesicNaturalVelocityPathAgrees :
    ∀ p q t : ℝ,
      bernoulliExponentialGeodesicNaturalVelocityPath p q t =
        (1 - t) * bernoulliLogOdds p + t * bernoulliLogOdds q
  exponentialGeodesicNaturalConstantVelocity :
    ∀ p q t : ℝ,
      HasDerivAt
        (fun τ : ℝ =>
          bernoulliLogOdds (bernoulliExponentialGeodesic p q τ))
        (bernoulliLogOdds q - bernoulliLogOdds p) t
  naturalFisherTensorSymmetric :
    ∀ θ u v : ℝ,
      bernoulliNaturalFisherTensor θ u v =
        bernoulliNaturalFisherTensor θ v u
  naturalFisherTensorDiagPositive :
    ∀ {θ u : ℝ}, u ≠ 0 → 0 < bernoulliNaturalFisherTensor θ u u
  naturalFisherTensorZero :
    ∀ u v : ℝ, bernoulliNaturalFisherTensor 0 u v = (1 / 4) * u * v
  fisherTensorPullbackLogOdds :
    ∀ θ u v : ℝ,
      bernoulliFisherTensor (bernoulliNaturalToMean θ)
          (bernoulliNaturalToMean θ * (1 - bernoulliNaturalToMean θ) * u)
          (bernoulliNaturalToMean θ * (1 - bernoulliNaturalToMean θ) * v) =
        bernoulliNaturalFisherTensor θ u v
  mixtureConnectionCoeffZero :
    ∀ p : ℝ, bernoulliMixtureConnectionCoeff p = 0
  exponentialConnectionCoeffZero :
    ∀ θ : ℝ, bernoulliExponentialConnectionCoeff θ = 0
  leviCivitaMeanConnectionCoeffHalf :
    bernoulliLeviCivitaMeanConnectionCoeff (1 / 2) = 0
  squaredHellingerNonnegative :
    ∀ p q : ℝ, 0 ≤ bernoulliSquaredHellinger p q
  squaredHellingerSymmetric :
    ∀ p q : ℝ, bernoulliSquaredHellinger p q = bernoulliSquaredHellinger q p
  squaredHellingerSelfZero :
    ∀ p : ℝ, bernoulliSquaredHellinger p p = 0
  klSelfZero :
    ∀ {p : ℝ}, 0 < p → p < 1 → bernoulliKL p p = 0
  jeffreysSymmetric :
    ∀ p q : ℝ, bernoulliJeffreys p q = bernoulliJeffreys q p
  jeffreysSelfZero :
    ∀ {p : ℝ}, 0 < p → p < 1 → bernoulliJeffreys p p = 0
  logOddsHalf :
    bernoulliLogOdds (1 / 2) = 0
  bornPositiveHellinger :
    ∀ {p : ℝ}, 0 ≤ p →
      bernoulliBornPositive (bernoulliHellingerEmbedding p) = p
  bornNegativeHellinger :
    ∀ {p : ℝ}, p ≤ 1 →
      bernoulliBornNegative (bernoulliHellingerEmbedding p) = 1 - p
  phaseForgetNotInjective :
    ¬ Function.Injective BinaryPhasedAmplitude.forgetPhase
  revisionStrengthMixture :
    ∀ (e₁ e₂ : BinaryCounts),
      e₁.total ≠ 0 → e₂.total ≠ 0 → e₁.total + e₂.total ≠ 0 →
        (e₁.add e₂).strength =
          (e₁.strength * e₁.total + e₂.strength * e₂.total) /
            (e₁.total + e₂.total)
  truthLogOddsTensorAdd :
    ∀ (x y : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence),
      x.neg ≠ 0 → y.neg ≠ 0 →
      x.truthOdds ≠ 0 → y.truthOdds ≠ 0 →
      x.truthOdds ≠ ⊤ → y.truthOdds ≠ ⊤ →
        (x * y).truthLogOdds = x.truthLogOdds + y.truthLogOdds
  meanConcentrationCoordinates : MeanConcentrationProfile

/-- The current finite Bernoulli/Beta information-geometry package.  It
records the Hellinger circle embedding, Fisher metric positivity, KL
self-zero, derivative-backed m/e geodesic velocities, m-flat revision,
e-flat tensor/log-odds composition, and the mean/concentration coordinate
surface. -/
noncomputable def informationGeometryLiftProfile : InformationGeometryLiftProfile where
  naturalToMeanPositive :=
    bernoulliNaturalToMean_pos
  naturalToMeanLtOne :=
    bernoulliNaturalToMean_lt_one
  logOddsNaturalToMean :=
    bernoulliLogOdds_naturalToMean
  naturalToMeanLogOdds := by
    intro p hp0 hp1
    exact bernoulliNaturalToMean_logOdds hp0 hp1
  hellingerUnitCircle := by
    intro p hp0 hp1
    exact bernoulliHellingerEmbedding_unit_circle hp0 hp1
  fisherMetricPositive := by
    intro p hp0 hp1
    exact bernoulliFisherMetric_pos hp0 hp1
  fisherMetricHalf :=
    bernoulliFisherMetric_half
  fisherTensorSymmetric :=
    bernoulliFisherTensor_symm
  fisherTensorDiagPositive := by
    intro p v hp0 hp1 hv
    exact bernoulliFisherTensor_diag_pos hp0 hp1 hv
  fisherTensorHalf :=
    bernoulliFisherTensor_half
  mixtureGeodesicOpen := by
    intro p q t hp0 hp1 hq0 hq1 ht0 ht1
    exact bernoulliMixtureGeodesic_in_open_simplex
      hp0 hp1 hq0 hq1 ht0 ht1
  exponentialGeodesicOpen :=
    bernoulliExponentialGeodesic_in_open_simplex
  exponentialGeodesicNaturalLinear :=
    bernoulliLogOdds_exponentialGeodesic
  mixtureGeodesicVelocityPathAgrees :=
    bernoulliMixtureGeodesicVelocityPath_eq_geodesic
  mixtureGeodesicConstantVelocity :=
    bernoulliMixtureGeodesic_hasDerivAt
  exponentialGeodesicNaturalVelocityPathAgrees :=
    bernoulliExponentialGeodesicNaturalVelocityPath_eq_linear
  exponentialGeodesicNaturalConstantVelocity :=
    bernoulliLogOdds_exponentialGeodesic_hasDerivAt
  naturalFisherTensorSymmetric :=
    bernoulliNaturalFisherTensor_symm
  naturalFisherTensorDiagPositive := by
    intro θ u hu
    exact bernoulliNaturalFisherTensor_diag_pos hu
  naturalFisherTensorZero :=
    bernoulliNaturalFisherTensor_zero
  fisherTensorPullbackLogOdds :=
    bernoulliFisherTensor_pullback_logOdds
  mixtureConnectionCoeffZero :=
    bernoulliMixtureConnectionCoeff_zero
  exponentialConnectionCoeffZero :=
    bernoulliExponentialConnectionCoeff_zero
  leviCivitaMeanConnectionCoeffHalf :=
    bernoulliLeviCivitaMeanConnectionCoeff_half
  squaredHellingerNonnegative :=
    bernoulliSquaredHellinger_nonneg
  squaredHellingerSymmetric :=
    bernoulliSquaredHellinger_symm
  squaredHellingerSelfZero :=
    bernoulliSquaredHellinger_self
  klSelfZero := by
    intro p hp0 hp1
    exact bernoulliKL_self hp0 hp1
  jeffreysSymmetric :=
    bernoulliJeffreys_symm
  jeffreysSelfZero := by
    intro p hp0 hp1
    exact bernoulliJeffreys_self hp0 hp1
  logOddsHalf :=
    bernoulliLogOdds_half
  bornPositiveHellinger := by
    intro p hp0
    exact bernoulliBornPositive_hellinger hp0
  bornNegativeHellinger := by
    intro p hp1
    exact bernoulliBornNegative_hellinger hp1
  phaseForgetNotInjective :=
    binaryPhasedAmplitude_forgetPhase_not_injective
  revisionStrengthMixture :=
    binaryRevisionStrength_is_mixture_coordinate
  truthLogOddsTensorAdd := by
    intro x y hx_neg hy_neg hx0 hy0 hxTop hyTop
    exact binaryTruthLogOdds_tensor_is_natural_coordinate
      x y hx_neg hy_neg hx0 hy0 hxTop hyTop
  meanConcentrationCoordinates :=
    meanConcentrationProfile

/-! ## Amplitude/phase extension boundary -/

/-- Amplitude/phase PLN boundary profile.

This profile connects the current classical PLN truth-value tower to a possible
amplitude extension without overclaiming that such an extension is complete:
standard PLN is the Born shadow of a phaseless/forgotten-amplitude projection,
relative phase is invisible to the standard typed-STV view, coherent
interference differs from incoherent probability addition, and the
two-dimensional KS-style algebra carrier selected by positive-definite norm is
the complex/negative-`μ` carrier. -/
structure AmplitudePhasePLNProfile where
  bornStrengthFromHellinger :
    ∀ {p concentration phase : ℝ}, 0 ≤ p →
      (BinaryAmplitudePhaseState.fromStrengthConcentration
        p concentration phase).bornStrength = p
  bornCounterStrengthFromHellinger :
    ∀ {p concentration phase : ℝ}, p ≤ 1 →
      (BinaryAmplitudePhaseState.fromStrengthConcentration
        p concentration phase).bornCounterStrength = 1 - p
  countsBornStrength :
    ∀ (e : BinaryCounts), 0 < e.total → ∀ phase : ℝ,
      (BinaryAmplitudePhaseState.fromCounts e phase).bornStrength =
        e.strength
  countsBornCounterStrength :
    ∀ (e : BinaryCounts), 0 < e.total → ∀ phase : ℝ,
      (BinaryAmplitudePhaseState.fromCounts e phase).bornCounterStrength =
        1 - e.strength
  countsProjectToStandardStrength :
    ∀ (χ : EvidenceWeightCoordinate) (e : BinaryCounts),
      0 < e.total → ∀ phase : ℝ,
        ((BinaryAmplitudePhaseState.fromCounts e phase).toTypedSTV χ).strength =
          e.strength
  countsProjectToStandardConfidence :
    ∀ (χ : EvidenceWeightCoordinate) (e : BinaryCounts) (phase : ℝ),
      ((BinaryAmplitudePhaseState.fromCounts e phase).toTypedSTV χ).confidence =
        TypedConfidence.ofWeight χ e.total
  phaseNotVisibleToStandardPLN :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let a := BinaryAmplitudePhaseState.fromStrengthConcentration (1 / 2) 1 0
    let b := BinaryAmplitudePhaseState.fromStrengthConcentration (1 / 2) 1 1
    a ≠ b ∧ a.toTypedSTV χ = b.toTypedSTV χ
  phaseForgetNotInjective :
    ¬ Function.Injective BinaryPhasedAmplitude.forgetPhase
  coherentWeightInterferenceLaw :
    ∀ r s cosDelta : ℝ,
      coherentTwoPathWeight r s cosDelta =
        incoherentTwoPathWeight r s + 2 * r * s * cosDelta
  zeroInterferenceIsIncoherent :
    ∀ r s : ℝ, coherentTwoPathWeight r s 0 = incoherentTwoPathWeight r s
  constructiveInterferenceCanary :
    coherentTwoPathWeight 1 1 1 ≠ incoherentTwoPathWeight 1 1
  destructiveInterferenceCanary :
    coherentTwoPathWeight 1 1 (-1) ≠ incoherentTwoPathWeight 1 1
  phaseFactorIsExponential :
    ∀ θ : ℝ, complexPhaseFactor θ = Complex.exp ((θ : ℂ) * Complex.I)
  complexAmplitudeIsExponential :
    ∀ r θ : ℝ, complexAmplitude r θ =
      (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  complexPhaseFactorUnitWeight :
    ∀ θ : ℝ, Complex.normSq (complexPhaseFactor θ) = 1
  complexAmplitudeBornWeight :
    ∀ r θ : ℝ, Complex.normSq (complexAmplitude r θ) = r ^ 2
  complexHellingerBornWeight :
    ∀ {p θ : ℝ}, 0 ≤ p →
      Complex.normSq (complexHellingerAmplitude p θ) = p
  complexTwoPathInterferenceLaw :
    ∀ r s θ φ : ℝ,
      complexTwoPathBornWeight r s θ φ =
        r ^ 2 + s ^ 2 + 2 * r * s * Real.cos (θ - φ)
  complexTwoPathReducesToCoherentWeight :
    ∀ r s θ φ : ℝ,
      complexTwoPathBornWeight r s θ φ =
        coherentTwoPathWeight r s (Real.cos (θ - φ))
  complexConstructiveInterference :
    complexTwoPathBornWeight 1 1 0 0 = 4
  complexDestructiveInterference :
    complexTwoPathBornWeight 1 1 0 Real.pi = 0
  ksComplexCarrierEquivComplex :
    KSComplexPhaseCarrier ≃+* ℂ
  ksComplexCarrierPositiveDefinite :
    ∀ z : KSComplexPhaseCarrier,
      0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)
  dualCarrierFailsPositiveDefinite :
    ¬ ∀ z : MuAlgebra 0,
      0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)
  splitCarrierFailsPositiveDefinite :
    ¬ ∀ z : MuAlgebra 1,
      0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)

/-- The current amplitude/phase boundary package. -/
noncomputable def amplitudePhasePLNProfile : AmplitudePhasePLNProfile where
  bornStrengthFromHellinger := by
    intro p concentration phase hp0
    exact BinaryAmplitudePhaseState.fromStrengthConcentration_bornStrength hp0
  bornCounterStrengthFromHellinger := by
    intro p concentration phase hp1
    exact BinaryAmplitudePhaseState.fromStrengthConcentration_bornCounterStrength hp1
  countsBornStrength :=
    BinaryAmplitudePhaseState.fromCounts_bornStrength
  countsBornCounterStrength :=
    BinaryAmplitudePhaseState.fromCounts_bornCounterStrength
  countsProjectToStandardStrength := by
    intro χ e hTotal phase
    exact BinaryAmplitudePhaseState.fromCounts_toTypedSTV_strength
      χ e hTotal phase
  countsProjectToStandardConfidence :=
    BinaryAmplitudePhaseState.fromCounts_toTypedSTV_confidence
  phaseNotVisibleToStandardPLN :=
    BinaryAmplitudePhaseState.phase_not_visible_to_standard_pln_view
  phaseForgetNotInjective :=
    binaryPhasedAmplitude_forgetPhase_not_injective
  coherentWeightInterferenceLaw :=
    coherentTwoPathWeight_eq_incoherent_plus_interference
  zeroInterferenceIsIncoherent :=
    coherentTwoPathWeight_zero_interference
  constructiveInterferenceCanary :=
    constructiveInterference_differs_from_incoherent
  destructiveInterferenceCanary :=
    destructiveInterference_differs_from_incoherent
  phaseFactorIsExponential :=
    complexPhaseFactor_eq_exp_mul_I
  complexAmplitudeIsExponential :=
    complexAmplitude_eq_real_mul_exp_mul_I
  complexPhaseFactorUnitWeight :=
    complexPhaseFactor_normSq
  complexAmplitudeBornWeight :=
    complexAmplitude_normSq
  complexHellingerBornWeight := by
    intro p θ hp
    exact complexHellingerAmplitude_normSq hp
  complexTwoPathInterferenceLaw :=
    complexTwoPathBornWeight_interference
  complexTwoPathReducesToCoherentWeight :=
    complexTwoPathBornWeight_eq_coherentWeight
  complexConstructiveInterference :=
    complexTwoPath_constructive_at_equal_phase
  complexDestructiveInterference :=
    complexTwoPath_destructive_at_pi
  ksComplexCarrierEquivComplex :=
    ksComplexPhaseCarrierEquivComplex
  ksComplexCarrierPositiveDefinite :=
    ksComplexPhaseCarrier_positiveDefinite
  dualCarrierFailsPositiveDefinite :=
    dualCarrier_not_positiveDefinite
  splitCarrierFailsPositiveDefinite :=
    splitCarrier_not_positiveDefinite

/-- Typed ITV operation profile: operations either require same semantics or
an explicit bridge to a shared target semantics. -/
structure TypedITVOperationProfile where
  sameSemanticsConjunction :
    ∀ {Sem : ITVSemantics.{0}} (x y : TypedITV Sem),
      (TypedITV.conjunctionSameSemantics x y).value =
        ITV.conjunction x.value y.value
  sameSemanticsImplication :
    ∀ {Sem : ITVSemantics.{0}} (x y : TypedITV Sem),
      (TypedITV.implicationSameSemantics x y).value =
        ITV.implication x.value y.value
  forgetToGenericPreservesValue :
    ∀ {Sem : ITVSemantics.{0}} (x : TypedITV Sem),
      (TypedITV.forgetToGeneric x).value = x.value
  crossSemanticsConjunctionViaBridge :
    ∀ {Sem₁ Sem₂ Target : ITVSemantics.{0}}
      (B : TypedITV.Bridge Sem₁ Sem₂ Target)
      (x : TypedITV Sem₁) (y : TypedITV Sem₂),
      (TypedITV.conjunctionViaBridge B x y).value =
        ITV.conjunction (B.left x).value (B.right y).value

/-- Typed operation profile: no silent cross-semantics mixing. -/
def typedITVOperationProfile : TypedITVOperationProfile where
  sameSemanticsConjunction :=
    typed_itv_same_semantics_conjunction_raw_value
  sameSemanticsImplication :=
    typed_itv_same_semantics_implication_raw_value
  forgetToGenericPreservesValue :=
    typed_itv_forget_to_generic_preserves_raw_value
  crossSemanticsConjunctionViaBridge :=
    typed_itv_cross_semantics_conjunction_via_bridge_raw_value

/-- World-model typed ITV profile: the world model extracts evidence as the
load-bearing state, typed ITV queries retain constructor provenance, and the
old raw query functions are exactly the forgetful projections. -/
structure WorldModelTypedITVProfile where
  binaryForgetsToRaw :
    ∀ {State Query Ctx : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).value =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITV
          (State := State) (Query := Query) sem ctx W q
  binaryTypedLowerIsRawLower :
    ∀ {State Query Ctx : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).lower =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVLower
          (State := State) (Query := Query) sem ctx W q
  binaryTypedUpperIsRawUpper :
    ∀ {State Query Ctx : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).upper =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVUpper
          (State := State) (Query := Query) sem ctx W q
  binaryTypedStrengthIsRawStrength :
    ∀ {State Query Ctx : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).midpoint =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVStrength
          (State := State) (Query := Query) sem ctx W q
  binaryTypedWidthIsRawWidth :
    ∀ {State Query Ctx : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).width =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVWidth
          (State := State) (Query := Query) sem ctx W q
  binaryTypedCredibilityIsRawCredibility :
    ∀ {State Query Ctx : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).credibility =
        Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVCredibility
          (State := State) (Query := Query) sem ctx W q
  binaryTypedJudgmentForgetsToRaw :
    ∀ {State Query Ctx : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) {W : State} {q : Query}
      {itv : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNWorldModel.ITVSemantics.toTruthTowerSemantics sem ctx)},
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.WMTypedITVJudgment
        (State := State) (Query := Query) sem ctx W q itv →
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.WMITVJudgment
        (State := State) (Query := Query) sem ctx W q itv.value
  binaryWalleyWidthComplement :
    ∀ {State Query : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (ctx : Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext)
      (W : State) (q : Query),
      (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITVWalley
          (State := State) (Query := Query) ctx W q).width +
        (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITVWalley
          (State := State) (Query := Query) ctx W q).credibility = 1
  sigmaForgetsToRaw :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).value =
        Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedAtForgetsToRawAt :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) {s : Srt} (q : Query s),
      (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITVAt
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).value =
        Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVAt
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedLowerIsRawLower :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).lower =
        Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVLower
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedUpperIsRawUpper :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).upper =
        Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVUpper
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedStrengthIsRawStrength :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).midpoint =
        Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVStrength
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedWidthIsRawWidth :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).width =
        Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVWidth
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedCredibilityIsRawCredibility :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).credibility =
        Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVCredibility
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  sigmaTypedJudgmentForgetsToRaw :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) {W : State} {q : Sigma Query}
      {itv : Mettapedia.Logic.PLNTruthTower.TypedITV
        (Mettapedia.Logic.PLNWorldModel.ITVSemantics.toTruthTowerSemantics sem ctx)},
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.WMTypedITVJudgmentSigma
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q itv →
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.WMITVJudgmentSigma
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q itv.value
  sigmaQueryEquivalencePreservesTypedITV :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      {q₁ q₂ : Sigma Query}
      (_ : Mettapedia.Logic.PLNWorldModel.WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := Srt) (Query := Query) q₁ q₂)
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State),
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q₁ =
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q₂
  sigmaRewriteProducesTypedJudgment :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) {r :
        Mettapedia.Logic.PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query}
      {W : State}, r.side → Mettapedia.Logic.PLNWorldModel.WMJudgment W →
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.WMTypedITVJudgmentSigma
        (State := State) (Srt := Srt) (Query := Query) sem ctx
        W r.conclusion
        (Mettapedia.Logic.PLNWorldModel.ITVSemantics.typedEval sem ctx (r.derive W))
  sigmaWalleyWidthComplement :
    ∀ {State Srt : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (ctx : Mettapedia.Logic.PLNWorldModel.IDMPredictiveContext)
      (W : State) (q : Sigma Query),
      (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITVWalley
          (State := State) (Srt := Srt) (Query := Query) ctx W q).width +
        (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITVWalley
          (State := State) (Srt := Srt) (Query := Query) ctx W q).credibility = 1

/-- World-model ITV profile: typed provenance is now available at the query
boundary, with raw ITV queries retained only as forgetful views. -/
def worldModelTypedITVProfile : WorldModelTypedITVProfile where
  binaryForgetsToRaw :=
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_value_eq_queryITV
  binaryTypedLowerIsRawLower :=
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_lower_eq_queryITVLower
  binaryTypedUpperIsRawUpper :=
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_upper_eq_queryITVUpper
  binaryTypedStrengthIsRawStrength :=
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_strength_eq_queryITVStrength
  binaryTypedWidthIsRawWidth :=
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_width_eq_queryITVWidth
  binaryTypedCredibilityIsRawCredibility :=
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_credibility_eq_queryITVCredibility
  binaryTypedJudgmentForgetsToRaw :=
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.WMTypedITVJudgment.forget
  binaryWalleyWidthComplement :=
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITVWalley_width_add_credibility
  sigmaForgetsToRaw :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_value_eq_queryITV
  sigmaTypedAtForgetsToRawAt :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITVAt_value_eq_queryITVAt
  sigmaTypedLowerIsRawLower :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_lower_eq_queryITVLower
  sigmaTypedUpperIsRawUpper :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_upper_eq_queryITVUpper
  sigmaTypedStrengthIsRawStrength :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_strength_eq_queryITVStrength
  sigmaTypedWidthIsRawWidth :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_width_eq_queryITVWidth
  sigmaTypedCredibilityIsRawCredibility :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_credibility_eq_queryITVCredibility
  sigmaTypedJudgmentForgetsToRaw :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.WMTypedITVJudgmentSigma.forget
  sigmaQueryEquivalencePreservesTypedITV :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.WMQueryEqSigma.to_queryTypedITV
  sigmaRewriteProducesTypedJudgment :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma.applyTypedITV
  sigmaWalleyWidthComplement :=
    Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITVWalley_width_add_credibility

/-- Credal/lower-prevision profile: lower and upper projections are forced by
the retained imprecise-probability object. -/
structure CredalForcedQueryProfile where
  lowerForced :
    ∀ {World Ω : Type} [Fintype Ω]
      (credal :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, credal W₁ = credal W₂ →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (credal W₁) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (credal W₂) f
  upperForced :
    ∀ {World Ω : Type} [Fintype Ω]
      (credal :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, credal W₁ = credal W₂ →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (credal W₁) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (credal W₂) f
  envelopeForced :
    ∀ {World Ω : Type} [Fintype Ω]
      (credal :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, credal W₁ = credal W₂ →
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (credal W₁) f,
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (credal W₁) f) =
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (credal W₂) f,
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (credal W₂) f)
  lowerPrevisionForced :
    ∀ {World Ω : Type}
      (prevision :
        World → Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
      {W₁ W₂ : World}, prevision W₁ = prevision W₂ →
        prevision W₁ X = prevision W₂ X
  upperPrevisionForced :
    ∀ {World Ω : Type}
      (prevision :
        World → Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
      {W₁ W₂ : World}, prevision W₁ = prevision W₂ →
        (prevision W₁).conjugate X = (prevision W₂).conjugate X
  desirableSetForced :
    ∀ {World Ω : Type}
      (desirable :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, desirable W₁ = desirable W₂ →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          (desirable W₁) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          (desirable W₂) f
  typedEnvelopeLowerForced :
    ∀ {Ω : Type} [Fintype Ω]
      (src : Mettapedia.Logic.PLNTruthTower.CredalEnvelopeITVSource Ω),
      (Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope src).lower =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          src.credal src.gamble
  typedEnvelopeUpperForced :
    ∀ {Ω : Type} [Fintype Ω]
      (src : Mettapedia.Logic.PLNTruthTower.CredalEnvelopeITVSource Ω),
      (Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope src).upper =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          src.credal src.gamble
  typedEnvelopeCredibilitySelected :
    ∀ {Ω : Type} [Fintype Ω]
      (src : Mettapedia.Logic.PLNTruthTower.CredalEnvelopeITVSource Ω),
      (Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope src).credibility =
        src.credibility
  typedEnvelopeBoundsDoNotForceCredibility :
    ∀ {Ω : Type} [Fintype Ω]
      (K :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK : K.Nonempty)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hf : ∀ ω, f ω ∈ Set.Icc 0 1),
      let x : Mettapedia.Logic.PLNTruthTower.TypedITV
          (Mettapedia.Logic.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
        Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope
          { credal := K
            gamble := f
            credal_nonempty := hK
            gamble_in_unit := hf
            credibility := 0
            credibility_in_unit := by norm_num }
      let y : Mettapedia.Logic.PLNTruthTower.TypedITV
          (Mettapedia.Logic.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
        Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope
          { credal := K
            gamble := f
            credal_nonempty := hK
            gamble_in_unit := hf
            credibility := 1
            credibility_in_unit := by norm_num }
      x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility
  typedLowerPrevisionLowerForced :
    ∀ {Ω : Type}
      (src : Mettapedia.Logic.PLNTruthTower.LowerPrevisionITVSource Ω),
      (Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision src).lower =
        src.prevision src.gamble
  typedLowerPrevisionUpperForced :
    ∀ {Ω : Type}
      (src : Mettapedia.Logic.PLNTruthTower.LowerPrevisionITVSource Ω),
      (Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision src).upper =
        src.prevision.conjugate src.gamble
  typedLowerPrevisionCredibilitySelected :
    ∀ {Ω : Type}
      (src : Mettapedia.Logic.PLNTruthTower.LowerPrevisionITVSource Ω),
      (Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision src).credibility =
        src.credibility
  typedLowerPrevisionBoundsDoNotForceCredibility :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω)
      (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1),
      let x : Mettapedia.Logic.PLNTruthTower.TypedITV
          (Mettapedia.Logic.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
        Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision
          { prevision := P
            gamble := X
            gamble_in_unit := hX
            credibility := 0
            credibility_in_unit := by norm_num }
      let y : Mettapedia.Logic.PLNTruthTower.TypedITV
          (Mettapedia.Logic.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
        Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision
          { prevision := P
            gamble := X
            gamble_in_unit := hX
            credibility := 1
            credibility_in_unit := by norm_num }
      x.lower = y.lower ∧ x.upper = y.upper ∧ x.credibility ≠ y.credibility
  singletonCredalLowerPrevisionAgreement :
    ∀ {Ω : Type} [Fintype Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.ProbDist Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
      (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1),
      let lp : Mettapedia.Logic.PLNTruthTower.TypedITV
          (Mettapedia.Logic.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
        Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision
          (Mettapedia.Logic.PLNTruthTower.SingletonCredalLowerPrevision.source
            P X hX credibility hc);
      let ce : Mettapedia.Logic.PLNTruthTower.TypedITV
          (Mettapedia.Logic.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
        Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope
          (Mettapedia.Logic.PLNTruthTower.SingletonCredalLowerPrevision.credalEnvelopeSource
            P X hX credibility hc);
      lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
        lp.credibility = ce.credibility
  finiteCredalLowerPrevisionAgreement :
    ∀ {Ω : Type} [Fintype Ω]
      (K :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK : K.Nonempty)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
      (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1),
      let lp : Mettapedia.Logic.PLNTruthTower.TypedITV
          (Mettapedia.Logic.PLNTruthTower.lowerPrevisionITVSemantics Ω) :=
        Mettapedia.Logic.PLNTruthTower.TypedITV.fromLowerPrevision
          (Mettapedia.Logic.PLNTruthTower.FiniteCredalLowerPrevision.source
            K hK X hX credibility hc);
      let ce : Mettapedia.Logic.PLNTruthTower.TypedITV
          (Mettapedia.Logic.PLNTruthTower.credalEnvelopeITVSemantics Ω) :=
        Mettapedia.Logic.PLNTruthTower.TypedITV.fromCredalEnvelope
          { credal := K
            gamble := X
            credal_nonempty := hK
            gamble_in_unit := hX
            credibility := credibility
            credibility_in_unit := hc };
      lp.lower = ce.lower ∧ lp.upper = ce.upper ∧
        lp.credibility = ce.credibility
  regularLowerPrevisionInducesDesirableSet :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (_hReg :
        Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω
  regularLowerPrevisionDesirableMembership :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (hReg :
        Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      X ∈
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet
            P hReg).D ↔
        P X > 0
  finiteLowerPrevisionRegular :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P
  finiteLowerPrevisionInducesDesirableSet :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (_P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω
  finiteCredalLowerPrevisionDesirableMembership :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (K :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK : K.Nonempty)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      X ∈
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCredalCoherentDesirableSet
            K hK).D ↔
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K X > 0

/-- Credal/lower-prevision forced-query profile. -/
noncomputable def credalForcedQueryProfile : CredalForcedQueryProfile where
  lowerForced := by
    intro World Ω inst credal f W₁ W₂ h
    exact credal_lower_expectation_is_forced_by_credal_set credal f h
  upperForced := by
    intro World Ω inst credal f W₁ W₂ h
    exact credal_upper_expectation_is_forced_by_credal_set credal f h
  envelopeForced := by
    intro World Ω inst credal f W₁ W₂ h
    exact credal_envelope_is_forced_by_credal_set credal f h
  lowerPrevisionForced :=
    lower_prevision_value_is_forced_by_lower_prevision
  upperPrevisionForced :=
    upper_prevision_value_is_forced_by_lower_prevision
  desirableSetForced :=
    desirable_lower_prevision_is_forced_by_desirable_set
  typedEnvelopeLowerForced :=
    credal_envelope_typed_itv_lower_forced
  typedEnvelopeUpperForced :=
    credal_envelope_typed_itv_upper_forced
  typedEnvelopeCredibilitySelected :=
    credal_envelope_typed_itv_credibility_is_selected
  typedEnvelopeBoundsDoNotForceCredibility :=
    credal_envelope_bounds_do_not_force_confidence_coordinate
  typedLowerPrevisionLowerForced :=
    lower_prevision_typed_itv_lower_forced
  typedLowerPrevisionUpperForced :=
    lower_prevision_typed_itv_upper_forced
  typedLowerPrevisionCredibilitySelected :=
    lower_prevision_typed_itv_credibility_is_selected
  typedLowerPrevisionBoundsDoNotForceCredibility :=
    lower_prevision_bounds_do_not_force_confidence_coordinate
  singletonCredalLowerPrevisionAgreement :=
    singleton_credal_lower_prevision_itv_agrees
  finiteCredalLowerPrevisionAgreement :=
    finite_credal_lower_prevision_itv_agrees
  regularLowerPrevisionInducesDesirableSet :=
    regular_lower_prevision_induces_coherent_desirable_set
  regularLowerPrevisionDesirableMembership :=
    regular_lower_prevision_desirable_membership
  finiteLowerPrevisionRegular :=
    finite_lower_prevision_is_regular
  finiteLowerPrevisionInducesDesirableSet :=
    finite_lower_prevision_induces_coherent_desirable_set
  finiteCredalLowerPrevisionDesirableMembership := by
    intro Ω instΩ nonemptyΩ K hK X
    exact finite_credal_lower_prevision_desirable_membership K hK X

/-- Profile for the explicit credal projection tower: the credal set/query
forces lower and upper, while coordinate plus weight select displayed
confidence. -/
structure CredalProjectionTowerProfile where
  lowerForced :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω),
      t.toTypedITV.lower =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          t.credal t.gamble
  upperForced :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω),
      t.toTypedITV.upper =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          t.credal t.gamble
  credibilitySelectedByCoordinate :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω),
      t.toTypedITV.credibility = t.coordinate.encode t.weight
  confidenceDecodesWeight :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω),
      t.typedConfidence.weight = t.weight
  widthComplementBridgeForcesDisplay :
    ∀ {Ω : Type} [Fintype Ω]
      (t : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω),
      t.WidthComplementBridge →
        t.credibilityDisplay = 1 - t.toTypedITV.width
  sameWeightDifferentCoordinateCanary :
    ∀ {Ω : Type} [Fintype Ω]
      (K :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK : K.Nonempty)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hf : ∀ ω, f ω ∈ Set.Icc 0 1),
      let x : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K
          credal_nonempty := hK
          gamble := f
          gamble_in_unit := hf
          coordinate := plnOddsCoordinate 1 (by norm_num)
          coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
          weight := 1
          weight_nonneg := by norm_num }
      let y : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
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
        x.typedConfidence.weight = y.typedConfidence.weight
  sameCoordinateWeightForcesSameConfidence :
    ∀ {Ω : Type} [Fintype Ω]
      (K₁ K₂ :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hf : ∀ ω, f ω ∈ Set.Icc 0 1)
      (χ : EvidenceWeightCoordinate) (hχ : UnitIcoOnNonneg χ)
      (w : ℝ) (hw : 0 ≤ w),
      let x : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K₁
          credal_nonempty := hK₁
          gamble := f
          gamble_in_unit := hf
          coordinate := χ
          coordinate_unit := hχ
          weight := w
          weight_nonneg := hw }
      let y : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K₂
          credal_nonempty := hK₂
          gamble := f
          gamble_in_unit := hf
          coordinate := χ
          coordinate_unit := hχ
          weight := w
          weight_nonneg := hw }
      x.toTypedITV.credibility = y.toTypedITV.credibility ∧
        x.typedConfidence.weight = y.typedConfidence.weight
  sameConfidenceDifferentEnvelopeCanary :
    ∀ {Ω : Type} [Fintype Ω]
      (K₁ K₂ :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CredalSetFinite Ω)
      (hK₁ : K₁.Nonempty) (hK₂ : K₂.Nonempty)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (hf : ∀ ω, f ω ∈ Set.Icc 0 1)
      (χ : EvidenceWeightCoordinate) (hχ : UnitIcoOnNonneg χ)
      (w : ℝ) (hw : 0 ≤ w)
      (_hLower :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K₁ f ≠
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb K₂ f),
      let x : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
        { credal := K₁
          credal_nonempty := hK₁
          gamble := f
          gamble_in_unit := hf
          coordinate := χ
          coordinate_unit := hχ
          weight := w
          weight_nonneg := hw }
      let y : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Ω :=
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
          x.toTypedITV.lower ≠ y.toTypedITV.lower
  concreteBoolSameConfidenceDifferentEnvelopeCanary :
    let x : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Bool :=
      { credal := Set.singleton
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolFalseProbDist
        credal_nonempty :=
          ⟨Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolFalseProbDist, rfl⟩
        gamble :=
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTruthGamble
        gamble_in_unit :=
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    let y : Mettapedia.Logic.PLNTruthTower.CredalProjectionTower Bool :=
      { credal := Set.singleton
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTrueProbDist
        credal_nonempty :=
          ⟨Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTrueProbDist, rfl⟩
        gamble :=
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTruthGamble
        gamble_in_unit :=
          Mettapedia.Logic.PLNTruthTower.CredalProjectionTower.boolTruthGamble_in_unit
        coordinate := plnOddsCoordinate 1 (by norm_num)
        coordinate_unit := plnOddsCoordinate_encode_in_Ico 1 (by norm_num)
        weight := 1
        weight_nonneg := by norm_num }
    x.toTypedITV.credibility = y.toTypedITV.credibility ∧
      x.typedConfidence.weight = y.typedConfidence.weight ∧
      x.toTypedITV.lower = 0 ∧
      y.toTypedITV.lower = 1 ∧
      x.toTypedITV.lower ≠ y.toTypedITV.lower

/-- Credal projection tower profile. -/
def credalProjectionTowerProfile : CredalProjectionTowerProfile where
  lowerForced :=
    credal_projection_tower_lower_forced
  upperForced :=
    credal_projection_tower_upper_forced
  credibilitySelectedByCoordinate :=
    credal_projection_tower_credibility_selected
  confidenceDecodesWeight :=
    credal_projection_tower_confidence_decodes_weight
  widthComplementBridgeForcesDisplay :=
    credal_projection_width_complement_bridge_forces_display
  sameWeightDifferentCoordinateCanary :=
    credal_projection_same_weight_can_display_different_confidence
  sameCoordinateWeightForcesSameConfidence :=
    credal_projection_same_coordinate_weight_forces_same_confidence
  sameConfidenceDifferentEnvelopeCanary :=
    credal_projection_same_confidence_can_have_different_envelope
  concreteBoolSameConfidenceDifferentEnvelopeCanary :=
    credal_projection_bool_same_confidence_different_envelope

/-! ## Natural-extension discipline profile -/

/-- Conservative profile for the natural-extension side of the tower.  It
records the coherent desirable-gamble and lower-prevision laws currently
formalized, plus the induced-lower-prevision forcedness.  It does not claim the
full Walley natural-extension existence/representation theorem. -/
structure NaturalExtensionProfile where
  desirableAvoidsSureLoss :
    ∀ {Ω : Type}
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      ∀ f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω,
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble.StrictlyNegative f →
          f ∉ C.D
  desirablePositiveCone :
    ∀ {Ω : Type}
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      ∀ f g :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω,
        f ∈ C.D → g ∈ C.D → ∀ a b : ℝ, a > 0 → b > 0 →
          a • f + b • g ∈ C.D
  inducedLowerPrevisionForced :
    ∀ {World Ω : Type}
      (desirable :
        World →
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      {W₁ W₂ : World}, desirable W₁ = desirable W₂ →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          (desirable W₁) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          (desirable W₂) f
  finiteDesirableInducesLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω
  finiteDesirableLowerPrevisionApply :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      finite_desirable_set_induces_lower_prevision C X =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          C X
  finiteDesirableLowerPrevisionLowerBound :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω)
      (c : ℝ), (∀ ω, c ≤ X ω) →
        c ≤ finite_desirable_set_induces_lower_prevision C X
  finiteDesirableLowerPrevisionPositiveHomogeneous :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (r : ℝ) (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      0 ≤ r →
        finite_desirable_set_induces_lower_prevision C (r • X) =
          r * finite_desirable_set_induces_lower_prevision C X
  finiteDesirableLowerPrevisionSuperadditive :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      finite_desirable_set_induces_lower_prevision C X +
        finite_desirable_set_induces_lower_prevision C Y ≤
          finite_desirable_set_induces_lower_prevision C (X + Y)
  regularLowerPrevisionDesirableRoundTrip :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (hReg :
        Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.Regular P)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.coherentDesirableSet
          P hReg) X = P X
  finiteLowerPrevisionDesirableRoundTripApply :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      finite_desirable_set_induces_lower_prevision
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            P) X = P X
  finiteLowerPrevisionDesirableRoundTrip :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      finite_desirable_set_induces_lower_prevision
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            P) = P
  finiteStrictRoundTrip :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω
  finiteStrictRoundTripMem :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈ (finite_strict_roundtrip C).D ↔
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
          C X > 0
  finiteStrictRoundTripLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_desirable_set_induces_lower_prevision (finite_strict_roundtrip C) =
        finite_desirable_set_induces_lower_prevision C
  finiteStrictRoundTripIdempotent :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      (finite_strict_roundtrip (finite_strict_roundtrip C)).D =
        (finite_strict_roundtrip C).D
  finiteStrictRoundTripSubsetOriginal :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      (finite_strict_roundtrip C).D ⊆ C.D
  finiteStrictRoundTripBoundaryNotRecovered :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0 →
        X ∉ (finite_strict_roundtrip C).D
  finiteStrictRoundTripMembershipIffOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (_hArch : archimedean_desirable_set C)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈ (finite_strict_roundtrip C).D ↔ X ∈ C.D
  finiteStrictRoundTripSetEqOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set C →
        (finite_strict_roundtrip C).D = C.D
  finiteStrictRoundTripEqOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set C → finite_strict_roundtrip C = C
  finiteStrictRoundTripArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set (finite_strict_roundtrip C)
  finiteStrictRoundTripEqIffArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_strict_roundtrip C = C ↔ archimedean_desirable_set C
  finiteDesirableLowerPrevisionMonotoneOfSubset :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      C.D ⊆ D.D →
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω,
          finite_desirable_set_induces_lower_prevision C X ≤
            finite_desirable_set_induces_lower_prevision D X
  finiteStrictRoundTripMonotone :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      C.D ⊆ D.D → (finite_strict_roundtrip C).D ⊆ (finite_strict_roundtrip D).D
  finiteStrictRoundTripGreatestArchimedeanSubset :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set D →
        D.D ⊆ C.D → D.D ⊆ (finite_strict_roundtrip C).D
  finiteStrictRoundTripArchimedeanSubsetIff :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set D →
        (D.D ⊆ (finite_strict_roundtrip C).D ↔ D.D ⊆ C.D)
  finiteStrictRoundTripFactorsThroughLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_desirable_set_induces_lower_prevision C =
          finite_desirable_set_induces_lower_prevision D →
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision C)).D =
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision D)).D
  finiteStrictRoundTripMembershipFactorsThroughLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_desirable_set_induces_lower_prevision C =
          finite_desirable_set_induces_lower_prevision D →
        ∀ X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω,
          X ∈
              (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
                (finite_desirable_set_induces_lower_prevision C)).D ↔
            X ∈
              (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
                (finite_desirable_set_induces_lower_prevision D)).D
  finiteDesirableRoundTripSubsetOriginal :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision C)).D ⊆ C.D
  finiteDesirableBoundaryNotRecovered :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        C X ≤ 0 →
        X ∉
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision C)).D
  finiteDesirableRoundTripMembershipIffOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω)
      (_hArch : archimedean_desirable_set C)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision C)).D ↔
        X ∈ C.D
  finiteDesirableRoundTripSetEqOfArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set C →
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision C)).D = C.D
  strictPositiveArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      archimedean_desirable_set (strict_positive_desirable_set Ω)
  strictPositiveRoundTripSetEq :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Ω))).D =
        (strict_positive_desirable_set Ω).D
  strictPositiveRoundTripMemIff :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision
              (strict_positive_desirable_set Ω))).D ↔
        (∀ ω, 0 < X ω)
  strictPositiveLowerPrevisionFiniteMinimum :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (strict_positive_desirable_set Ω) X =
          finite_minimum X
  closedPositiveLowerPrevisionFiniteMinimum :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (nonnegative_nonzero_desirable_set Ω) X =
          finite_minimum X
  positiveConesInduceSameLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (strict_positive_desirable_set Ω) X =
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (nonnegative_nonzero_desirable_set Ω) X
  positiveConesInduceSameFiniteLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Ω) =
        finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Ω)
  closedPositiveStrictRoundTripSetEq :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω],
      (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
        (finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Ω))).D =
        (strict_positive_desirable_set Ω).D
  closedPositiveStrictRoundTripMemIff :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      X ∈
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            (finite_desirable_set_induces_lower_prevision
              (nonnegative_nonzero_desirable_set Ω))).D ↔
        (∀ ω, 0 < X ω)
  boolBoundaryDesirable :
    bool_boundary_gamble ∈ (nonnegative_nonzero_desirable_set Bool).D
  boolBoundaryNotStrict :
    bool_boundary_gamble ∉ (strict_positive_desirable_set Bool).D
  boolPositiveConesDistinct :
    (strict_positive_desirable_set Bool).D ≠
      (nonnegative_nonzero_desirable_set Bool).D
  boolPositiveConesProjectionNotInjective :
    (strict_positive_desirable_set Bool).D ≠
        (nonnegative_nonzero_desirable_set Bool).D ∧
      finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Bool) =
        finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Bool)
  boolBoundaryLowerPrevisionEqZero :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
      (nonnegative_nonzero_desirable_set Bool) bool_boundary_gamble = 0
  boolBoundaryNotRecovered :
    bool_boundary_gamble ∈ (nonnegative_nonzero_desirable_set Bool).D ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerPrevision
        (nonnegative_nonzero_desirable_set Bool) bool_boundary_gamble = 0 ∧
      bool_boundary_gamble ∉
        (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
          (finite_desirable_set_induces_lower_prevision
            (nonnegative_nonzero_desirable_set Bool))).D
  boolBoundaryNotArchimedean :
    ¬ archimedean_desirable_set (nonnegative_nonzero_desirable_set Bool)
  boolBoundaryRoundTripSetNeOriginal :
    (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
      (finite_desirable_set_induces_lower_prevision
        (nonnegative_nonzero_desirable_set Bool))).D ≠
      (nonnegative_nonzero_desirable_set Bool).D
  lowerMonotone :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      {X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω},
      X ≤ Y → P X ≤ P Y
  lowerSuperadditive :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      P X + P Y ≤ P (X + Y)
  upperConjugateSubadditive :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X Y : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      P.conjugate (X + Y) ≤ P.conjugate X + P.conjugate Y
  imprecisionNonnegative :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω)
      (X : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble Ω),
      0 ≤ Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision P X

/-- Current natural-extension discipline profile. -/
noncomputable def naturalExtensionProfile : NaturalExtensionProfile where
  desirableAvoidsSureLoss :=
    coherent_desirable_set_avoids_sure_loss
  desirablePositiveCone :=
    coherent_desirable_set_is_positive_cone
  inducedLowerPrevisionForced :=
    desirable_lower_prevision_is_forced_by_desirable_set
  finiteDesirableInducesLowerPrevision :=
    finite_desirable_set_induces_lower_prevision
  finiteDesirableLowerPrevisionApply :=
    finite_desirable_lower_prevision_apply
  finiteDesirableLowerPrevisionLowerBound := by
    intro Ω instΩ nonemptyΩ C X c hc
    exact finite_desirable_lower_prevision_lower_bound C X c hc
  finiteDesirableLowerPrevisionPositiveHomogeneous := by
    intro Ω instΩ nonemptyΩ C r X hr
    exact finite_desirable_lower_prevision_pos_homog C r X hr
  finiteDesirableLowerPrevisionSuperadditive :=
    finite_desirable_lower_prevision_superadditive
  regularLowerPrevisionDesirableRoundTrip :=
    regular_lower_prevision_desirable_roundtrip
  finiteLowerPrevisionDesirableRoundTripApply :=
    finite_lower_prevision_desirable_roundtrip_apply
  finiteLowerPrevisionDesirableRoundTrip :=
    finite_lower_prevision_desirable_roundtrip
  finiteStrictRoundTrip :=
    @finite_strict_roundtrip
  finiteStrictRoundTripMem :=
    finite_strict_roundtrip_mem
  finiteStrictRoundTripLowerPrevision :=
    finite_strict_roundtrip_lower_prevision_eq
  finiteStrictRoundTripIdempotent :=
    finite_strict_roundtrip_idempotent_D
  finiteStrictRoundTripSubsetOriginal :=
    finite_strict_roundtrip_subset_original
  finiteStrictRoundTripBoundaryNotRecovered :=
    finite_strict_roundtrip_not_mem_of_nonpositive_lower_prevision
  finiteStrictRoundTripMembershipIffOfArchimedean :=
    finite_strict_roundtrip_mem_iff_of_archimedean
  finiteStrictRoundTripSetEqOfArchimedean :=
    finite_strict_roundtrip_D_eq_of_archimedean
  finiteStrictRoundTripEqOfArchimedean :=
    finite_strict_roundtrip_eq_of_archimedean
  finiteStrictRoundTripArchimedean :=
    finite_strict_roundtrip_archimedean
  finiteStrictRoundTripEqIffArchimedean :=
    finite_strict_roundtrip_eq_iff_archimedean
  finiteDesirableLowerPrevisionMonotoneOfSubset :=
    finite_desirable_lower_prevision_mono_of_subset
  finiteStrictRoundTripMonotone :=
    finite_strict_roundtrip_mono_D
  finiteStrictRoundTripGreatestArchimedeanSubset :=
    finite_strict_roundtrip_greatest_archimedean_subset_D
  finiteStrictRoundTripArchimedeanSubsetIff :=
    finite_strict_roundtrip_archimedean_subset_iff
  finiteStrictRoundTripFactorsThroughLowerPrevision :=
    same_finite_lower_prevision_same_strict_roundtrip_D
  finiteStrictRoundTripMembershipFactorsThroughLowerPrevision :=
    same_finite_lower_prevision_same_strict_roundtrip_mem_iff
  finiteDesirableRoundTripSubsetOriginal :=
    finite_desirable_roundtrip_subset_original
  finiteDesirableBoundaryNotRecovered :=
    finite_desirable_boundary_not_recovered
  finiteDesirableRoundTripMembershipIffOfArchimedean :=
    finite_desirable_roundtrip_mem_iff_of_archimedean
  finiteDesirableRoundTripSetEqOfArchimedean :=
    finite_desirable_roundtrip_D_eq_of_archimedean
  strictPositiveArchimedean :=
    strict_positive_desirable_set_archimedean
  strictPositiveRoundTripSetEq :=
    strict_positive_roundtrip_D_eq
  strictPositiveRoundTripMemIff :=
    strict_positive_roundtrip_mem_iff
  strictPositiveLowerPrevisionFiniteMinimum :=
    strict_positive_lower_prevision_eq_finite_minimum
  closedPositiveLowerPrevisionFiniteMinimum :=
    nonnegative_nonzero_lower_prevision_eq_finite_minimum
  positiveConesInduceSameLowerPrevision :=
    positive_cones_induce_same_lower_prevision
  positiveConesInduceSameFiniteLowerPrevision :=
    @positive_cones_induce_same_finite_lower_prevision
  closedPositiveStrictRoundTripSetEq :=
    @nonnegative_nonzero_strict_roundtrip_D_eq_strict_positive
  closedPositiveStrictRoundTripMemIff :=
    nonnegative_nonzero_strict_roundtrip_mem_iff
  boolBoundaryDesirable :=
    bool_boundary_gamble_desirable
  boolBoundaryNotStrict :=
    bool_boundary_gamble_not_strict
  boolPositiveConesDistinct :=
    bool_positive_cones_distinct
  boolPositiveConesProjectionNotInjective :=
    bool_positive_cones_projection_not_injective
  boolBoundaryLowerPrevisionEqZero :=
    bool_boundary_lower_prevision_eq_zero
  boolBoundaryNotRecovered :=
    bool_boundary_not_recovered_by_strict_roundtrip
  boolBoundaryNotArchimedean :=
    bool_nonnegative_nonzero_not_archimedean
  boolBoundaryRoundTripSetNeOriginal :=
    bool_boundary_roundtrip_set_ne_original
  lowerMonotone := by
    intro Ω P X Y h
    exact lower_prevision_is_monotone P h
  lowerSuperadditive :=
    lower_prevision_is_superadditive
  upperConjugateSubadditive :=
    upper_conjugate_prevision_is_subadditive
  imprecisionNonnegative :=
    lower_prevision_imprecision_is_nonnegative

/-! ## Core-four local completion profile -/

/-- Completion profile for the four finite/provenance threads Zar asked to
close locally:

1. confidence coordinate freedom/forcing;
2. strength projection taxonomy;
3. typed ITV provenance;
4. finite credal/lower-prevision/desirable-gamble loop.

This is a local finite/provenance completion package.  It deliberately does not
claim the full infinite Walley natural-extension theorem. -/
structure CoreFourCompletionProfile where
  confidence : ConfidenceFormulaAuditProfile
  confidenceReconstructionBoundary :
    ∀ (encode decode : ℝ → ℝ),
      CountReconstruction encode decode ↔ LeftInverseOnPositive encode decode
  confidenceWalleyBridgeForcesPLNOdds :
    ∀ (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s),
      WidthComplementCompatible χ s →
        ∀ {n : ℝ}, 0 ≤ n → χ.encode n = (plnOddsCoordinate s hs).encode n
  confidenceNonPLNCoordinateCanary :
    ∀ (s : ℝ) (hs : 0 < s),
      ¬ WidthComplementCompatible (reserveHalfCoordinate s hs) s
  strength : StrengthProjectionProfile
  strengthSelectorFreedom :
    ∃ itv : ITV,
      Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ∧
        Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .midpoint itv ≠
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv ∧
          Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .lower itv ≠
            Mettapedia.Logic.PLNForcedQueries.ITVSelector.eval .upper itv
  strengthTypedMidpointBounds :
    ∀ {Sem : Mettapedia.Logic.PLNTruthTower.ITVSemantics.{0}}
      (x : Mettapedia.Logic.PLNTruthTower.TypedITV Sem),
      x.lower ≤ x.midpoint ∧ x.midpoint ≤ x.upper ∧
        x.midpoint ∈ Set.Icc (0 : ℝ) 1
  typedITV : WorldModelTypedITVProfile
  typedBinaryRawCoordinateViews :
    ∀ {State Query Ctx : Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.BinaryWorldModel State Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Query),
      (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
          (State := State) (Query := Query) sem ctx W q).value =
          Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITV
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).lower =
          Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVLower
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).upper =
          Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVUpper
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).width =
          Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVWidth
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).credibility =
          Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVCredibility
            (State := State) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV
            (State := State) (Query := Query) sem ctx W q).midpoint =
          Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryITVStrength
            (State := State) (Query := Query) sem ctx W q
  typedSigmaRawCoordinateViews :
    ∀ {State Srt Ctx : Type} {Query : Srt → Type}
      [Mettapedia.Logic.EvidenceClass.EvidenceType State]
      [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
      (sem : Mettapedia.Logic.PLNWorldModel.ITVSemantics Ctx)
      (ctx : Ctx) (W : State) (q : Sigma Query),
      (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
          (State := State) (Srt := Srt) (Query := Query) sem ctx W q).value =
          Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).lower =
          Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVLower
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).upper =
          Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVUpper
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).width =
          Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVWidth
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).credibility =
          Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVCredibility
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q ∧
        (Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q).midpoint =
          Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryITVStrength
            (State := State) (Srt := Srt) (Query := Query) sem ctx W q
  finiteCredalLoop : NaturalExtensionProfile
  finiteLowerPrevisionToDesirableToLowerPrevision :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      finite_desirable_set_induces_lower_prevision
          (Mettapedia.Logic.PLNTruthTower.LowerPrevisionDesirableBridge.finiteCoherentDesirableSet
            P) = P
  finiteStrictRoundTripFixedIffArchimedean :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      finite_strict_roundtrip C = C ↔ archimedean_desirable_set C
  finiteStrictRoundTripGreatestArchimedeanSubset :
    ∀ {Ω : Type} [Fintype Ω] [Nonempty Ω]
      (C D :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.CoherentDesirableSet Ω),
      archimedean_desirable_set D →
        D.D ⊆ C.D → D.D ⊆ (finite_strict_roundtrip C).D
  finiteProjectionNonInjectivityCanary :
    (strict_positive_desirable_set Bool).D ≠
        (nonnegative_nonzero_desirable_set Bool).D ∧
      finite_desirable_set_induces_lower_prevision
          (strict_positive_desirable_set Bool) =
        finite_desirable_set_induces_lower_prevision
          (nonnegative_nonzero_desirable_set Bool)

/-- The verified local completion package for the first four threads. -/
noncomputable def coreFourCompletionProfile : CoreFourCompletionProfile where
  confidence := confidenceFormulaAuditProfile
  confidenceReconstructionBoundary :=
    reconstructive_confidence_coordinates_iff_left_inverse
  confidenceWalleyBridgeForcesPLNOdds := by
    intro χ s hs hχ n hn
    exact walley_width_complement_forces_pln_odds χ s hs hχ hn
  confidenceNonPLNCoordinateCanary :=
    reconstructive_coordinate_need_not_be_walley_compatible
  strength := strengthProjectionProfile
  strengthSelectorFreedom :=
    generic_itv_does_not_force_point_projection
  strengthTypedMidpointBounds := by
    intro Sem x
    exact ⟨typed_itv_lower_le_midpoint x, typed_itv_midpoint_le_upper x,
      typed_itv_midpoint_in_unit x⟩
  typedITV := worldModelTypedITVProfile
  typedBinaryRawCoordinateViews := by
    intro State Query Ctx instE instWM sem ctx W q
    exact ⟨Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_value_eq_queryITV
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_lower_eq_queryITVLower
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_upper_eq_queryITVUpper
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_width_eq_queryITVWidth
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_credibility_eq_queryITVCredibility
        (State := State) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryTypedITV_strength_eq_queryITVStrength
        (State := State) (Query := Query) sem ctx W q⟩
  typedSigmaRawCoordinateViews := by
    intro State Srt Ctx Query instE instWM sem ctx W q
    exact ⟨Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_value_eq_queryITV
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_lower_eq_queryITVLower
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_upper_eq_queryITVUpper
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_width_eq_queryITVWidth
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_credibility_eq_queryITVCredibility
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q,
      Mettapedia.Logic.PLNWorldModel.WorldModelSigma.queryTypedITV_strength_eq_queryITVStrength
        (State := State) (Srt := Srt) (Query := Query) sem ctx W q⟩
  finiteCredalLoop := naturalExtensionProfile
  finiteLowerPrevisionToDesirableToLowerPrevision :=
    finite_lower_prevision_desirable_roundtrip
  finiteStrictRoundTripFixedIffArchimedean :=
    finite_strict_roundtrip_eq_iff_archimedean
  finiteStrictRoundTripGreatestArchimedeanSubset :=
    finite_strict_roundtrip_greatest_archimedean_subset_D
  finiteProjectionNonInjectivityCanary :=
    bool_positive_cones_projection_not_injective

/-! ## Crispness and imprecision collapse -/

/-- Crispness is not a display choice.  It is forced exactly when the retained
precision object collapses: a unique `Θ`, a singleton credal set, or a precise
lower prevision.  Disagreement and incomparability are the corresponding
canaries that force honest interval/credal semantics. -/
structure CrispnessCollapseProfile where
  thetaSingletonCollapse :
    ∀ {α β : Type} [CompleteLattice β] (Θ₀ : α → β),
      Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.intervalOfFamily
        (Set.singleton Θ₀) = ⟨Θ₀, Θ₀⟩
  thetaSubsingletonLowerEqUpper :
    ∀ {α β : Type} [CompleteLattice β]
      {Θs : Set (α → β)},
      Θs.Subsingleton → Θs.Nonempty → ∀ x : α,
        Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.lower Θs x =
          Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.upper Θs x
  credalSingletonCollapse :
    ∀ (Ω : Type) [Fintype Ω]
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.ProbDist Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (Set.singleton P) f =
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
          (Set.singleton P) f
  credalDisagreementCreatesInterval :
    ∀ {Ω : Type} [Fintype Ω]
      (P Q : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.ProbDist Ω)
      (f : Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.Gamble Ω),
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.expectedValue P f <
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.expectedValue Q f →
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
            (Set.insert P (Set.singleton Q)) f <
          Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
            (Set.insert P (Set.singleton Q)) f
  lowerPrevisionZeroImprecisionIffPrecise :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      (∀ X, Mettapedia.ProbabilityTheory.ImpreciseProbability.imprecision P X = 0) ↔
        P.isPrecise
  lowerPrevisionPreciseIffAdditive :
    ∀ {Ω : Type}
      (P : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision Ω),
      P.isPrecise ↔ ∀ X Y, P (X + Y) = P X + P Y
  ksIncomparabilityBlocksCrispPoint :
    ∀ {α : Type}
      [KnuthSkilling.TotalityImprecision.PartialKnuthSkillingAlgebra α]
      (x y : α),
      KnuthSkilling.TotalityImprecision.PartialKnuthSkillingAlgebra.Incomparable
        x y →
        ¬ ∃ (Θ : α → ℝ), ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b

/-- Crispness-collapse profile: singleton/subsingleton completions collapse
to point semantics; singleton credal sets collapse; disagreement and
incomparability force interval semantics; lower-prevision precision is exactly
zero imprecision, equivalently additivity. -/
def crispnessCollapseProfile : CrispnessCollapseProfile where
  thetaSingletonCollapse :=
    thetaSingleton_collapses_to_point
  thetaSubsingletonLowerEqUpper := by
    intro α β inst Θs hsub hne x
    exact
      Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics.lower_eq_upper_of_subsingleton
        hsub hne x
  credalSingletonCollapse :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.V3_is_singleton_collapse
  credalDisagreementCreatesInterval := by
    intro Ω inst P Q f hPQ
    exact
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.V2_intervals_exist_general
        P Q f hPQ
  lowerPrevisionZeroImprecisionIffPrecise :=
    lowerPrevision_zero_imprecision_iff_precise
  lowerPrevisionPreciseIffAdditive :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision.precise_iff_additive
  ksIncomparabilityBlocksCrispPoint := by
    intro α inst x y hxy
    exact ks_incomparable_forces_no_faithful_point_representation x y hxy

/-! ## Degrees of freedom versus forcing capstone -/

/-- Capstone view of the current theory.  Each field is either a genuine
forcing law or an explicit canary showing a remaining degree of freedom.
This is the compact answer to: which coordinates are mathematical
consequences, and which are modeling choices? -/
structure DegreesOfFreedomForcingProfile where
  reconstructiveCoordinatesNeedLeftInverse :
    ∀ (encode decode : ℝ → ℝ),
      (∀ {nPlus nMinus : ℝ},
        0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
          (let n := nPlus + nMinus
           let stv : ℝ × ℝ := (nPlus / n, encode n)
           let m := decode stv.2
           (stv.1 * m, (1 - stv.1) * m)) = (nPlus, nMinus)) →
        ∀ {w : ℝ}, 0 < w → decode (encode w) = w
  reconstructiveCoordinatesIffLeftInverse :
    ∀ (encode decode : ℝ → ℝ),
      CountReconstruction encode decode ↔ LeftInverseOnPositive encode decode
  reconstructiveCoordinatesWithLeftInverseSuffice :
    ∀ (χ : EvidenceWeightCoordinate) {nPlus nMinus : ℝ},
      0 ≤ nPlus → 0 ≤ nMinus → nPlus + nMinus ≠ 0 →
        χ.decodeCounts (χ.encodeCounts nPlus nMinus) =
          (nPlus, nMinus)
  reconstructiveCoordinateCanFailWalleyBridge :
    ∀ (s : ℝ) (hs : 0 < s),
      ¬ WidthComplementCompatible (reserveHalfCoordinate s hs) s
  confidenceChartTorsor : ConfidenceChartTorsorProfile
  confidenceRevisionCharts : ConfidenceRevisionChartProfile
  confidenceFormulaAudit : ConfidenceFormulaAuditProfile
  informationGeometryLift : InformationGeometryLiftProfile
  amplitudePhaseBoundary : AmplitudePhasePLNProfile
  genericITVFreedom : GenericITVProfile
  bayesCredibilityNotBackendLevel : BayesCredibleProfile
  meanConcentrationLinkFreedom : MeanConcentrationProfile
  walleyBridgeForcesPLNOdds : WalleyBinaryProfile
  walleyCategoricalCredalLift : WalleyCategoricalProfile
  strengthProjectionForcing : StrengthProjectionProfile
  sufficientStatisticForcing : SufficientStatisticQueryProfile
  typedCompatibilityBoundary : TypedITVOperationProfile
  worldModelTypedITVBoundary : WorldModelTypedITVProfile
  credalProjectionForcing : CredalForcedQueryProfile
  credalProjectionTowerBoundary : CredalProjectionTowerProfile
  naturalExtensionDiscipline : NaturalExtensionProfile
  crispnessCollapseForcing : CrispnessCollapseProfile

/-- The current DOF/forcing capstone: reconstruction gives only invertibility;
generic ITVs leave width, credibility, and selector free; Bayes constructors
force the evidence-concentration coordinate but not interval backend/level;
Walley-IDM width complement forces PLN odds; and retained evidence/credal
objects force their canonical projections. -/
noncomputable def degreesOfFreedomForcingProfile : DegreesOfFreedomForcingProfile where
  reconstructiveCoordinatesNeedLeftInverse :=
    reconstructive_confidence_coordinates_need_left_inverse
  reconstructiveCoordinatesIffLeftInverse :=
    reconstructive_confidence_coordinates_iff_left_inverse
  reconstructiveCoordinatesWithLeftInverseSuffice :=
    evidence_weight_coordinate_suffices_for_binary_count_reconstruction
  reconstructiveCoordinateCanFailWalleyBridge :=
    reconstructive_coordinate_need_not_be_walley_compatible
  confidenceChartTorsor :=
    confidenceChartTorsorProfile
  confidenceRevisionCharts :=
    confidenceRevisionChartProfile
  confidenceFormulaAudit :=
    confidenceFormulaAuditProfile
  informationGeometryLift :=
    informationGeometryLiftProfile
  amplitudePhaseBoundary :=
    amplitudePhasePLNProfile
  genericITVFreedom :=
    genericITVProfile
  bayesCredibilityNotBackendLevel :=
    bayesCredibleProfile
  meanConcentrationLinkFreedom :=
    meanConcentrationProfile
  walleyBridgeForcesPLNOdds :=
    walleyBinaryProfile
  walleyCategoricalCredalLift :=
    walleyCategoricalProfile
  strengthProjectionForcing :=
    strengthProjectionProfile
  sufficientStatisticForcing :=
    sufficientStatisticQueryProfile
  typedCompatibilityBoundary :=
    typedITVOperationProfile
  worldModelTypedITVBoundary :=
    worldModelTypedITVProfile
  credalProjectionForcing :=
    credalForcedQueryProfile
  credalProjectionTowerBoundary :=
    credalProjectionTowerProfile
  naturalExtensionDiscipline :=
    naturalExtensionProfile
  crispnessCollapseForcing :=
    crispnessCollapseProfile

/-- Paper-facing DOF-vs-forcing synthesis.

This profile is intentionally redundant with the lower profiles: its purpose is
to provide a readable theorem map for exposition.  It separates the canonical
simplex/scale strength coordinate, the torsorial confidence-chart freedom, the
extra laws that pick the PLN chart, the mean/natural/concentration
information-geometry split, and the boundary where relative phase would be
additional structure beyond the current real Hellinger/Born shadow. -/
structure PaperFacingDOFForcingSynthesisProfile where
  strengthDirectionAndConcentration :
    MeanConcentrationProfile
  confidenceChartsHaveTorsorFreedom :
    ConfidenceChartTorsorProfile
  reconstructiveConfidenceIffLeftInverse :
    ∀ (encode decode : ℝ → ℝ),
      CountReconstruction encode decode ↔ LeftInverseOnPositive encode decode
  revisionAndCanonicalOddsPickPLN :
    ConfidenceRevisionChartProfile
  walleyWidthComplementPicksPLN :
    WalleyBinaryProfile
  betaPriorMeanAndConcentrationAreTheLearnableAxes :
    MeanConcentrationProfile
  bernoulliInformationGeometry :
    InformationGeometryLiftProfile
  amplitudePhaseExtensionBoundary :
    AmplitudePhasePLNProfile
  phaseIsExtraStructureBeyondClassicalAmplitude :
    ¬ Function.Injective BinaryPhasedAmplitude.forgetPhase
  fullDOFForcingWall :
    DegreesOfFreedomForcingProfile

/-- The current paper-facing synthesis theorem map. -/
noncomputable def paperFacingDOFForcingSynthesisProfile :
    PaperFacingDOFForcingSynthesisProfile where
  strengthDirectionAndConcentration :=
    meanConcentrationProfile
  confidenceChartsHaveTorsorFreedom :=
    confidenceChartTorsorProfile
  reconstructiveConfidenceIffLeftInverse :=
    reconstructive_confidence_coordinates_iff_left_inverse
  revisionAndCanonicalOddsPickPLN :=
    confidenceRevisionChartProfile
  walleyWidthComplementPicksPLN :=
    walleyBinaryProfile
  betaPriorMeanAndConcentrationAreTheLearnableAxes :=
    meanConcentrationProfile
  bernoulliInformationGeometry :=
    informationGeometryLiftProfile
  amplitudePhaseExtensionBoundary :=
    amplitudePhasePLNProfile
  phaseIsExtraStructureBeyondClassicalAmplitude :=
    binaryPhasedAmplitude_forgetPhase_not_injective
  fullDOFForcingWall :=
    degreesOfFreedomForcingProfile

/-- Compact paper-facing formula characterization profile.

This is the high-level theorem map: strength is the simplex direction;
confidence is a chart on concentration; chart freedom is torsorial until an
extra law chooses a member; revision and Walley laws distinguish the PLN chart;
and the Bernoulli/Beta IG slice separates mean, natural log-odds, and
concentration. -/
structure FormulaCharacterizationProfile where
  strengthAndConcentration : MeanConcentrationProfile
  confidenceChartTorsor : ConfidenceChartTorsorProfile
  confidenceRevisionAndForcing : ConfidenceRevisionChartProfile
  informationGeometry : InformationGeometryLiftProfile
  amplitudePhaseBoundary : AmplitudePhasePLNProfile
  degreesOfFreedomForcing : DegreesOfFreedomForcingProfile
  paperFacingSynthesis : PaperFacingDOFForcingSynthesisProfile

/-- The current paper-facing DOF-vs-forcing theorem map. -/
noncomputable def formulaCharacterizationProfile :
    FormulaCharacterizationProfile where
  strengthAndConcentration :=
    meanConcentrationProfile
  confidenceChartTorsor :=
    confidenceChartTorsorProfile
  confidenceRevisionAndForcing :=
    confidenceRevisionChartProfile
  informationGeometry :=
    informationGeometryLiftProfile
  amplitudePhaseBoundary :=
    amplitudePhasePLNProfile
  degreesOfFreedomForcing :=
    degreesOfFreedomForcingProfile
  paperFacingSynthesis :=
    paperFacingDOFForcingSynthesisProfile

/-! ## Confidence characterization endpoint -/

/-- Stable index-level alias for the finite singleton-posterior collapse
endpoint: compact predictive That's-All together with exact typed ITV
readouts. -/
theorem deFinetti_canonical_compactPredictiveThatsAll_and_prefixTypedWidthComplementITV_exact
    (M : Mettapedia.Logic.DeFinetti.BernoulliMixture) (k l n : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0)
    (G : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble (Fin n → Bool))
    (hG : ∀ ω, G ω ∈ Set.Icc (0 : ℝ) 1) :
    Mettapedia.Logic.ConceptOntology.compactPredictiveThatsAll
        (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.externalPathLawBoundedMeasurableCompactCredalSet
          ({Mettapedia.Logic.ConceptOntology.posteriorCanonicalExternalBoolProcessLaw M k l hZ} :
            Set (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw
              (ℕ → Bool)))) ∧
      (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).lower =
        Mettapedia.Logic.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G ∧
      (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).upper =
        Mettapedia.Logic.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G ∧
      (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).width = 0 ∧
      (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).credibility = 1 ∧
      (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).midpoint =
        Mettapedia.Logic.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G := by
  exact
    Mettapedia.Logic.ConceptOntology.posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_prefixTypedWidthComplementITV_exact
      M k l n hZ G hG

/-- Stable index-level alias for the proved infinite i.i.d. regime split: the
raw posterior process-law crown exists exactly in the zero-interior-mixing
regime. -/
theorem deFinetti_posterior_processLawCrown_iff_zeroInteriorMixingMass
    (M : Mettapedia.Logic.DeFinetti.BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.PosteriorBernoulliMixtureProcessLawCrown
      M k l hZ ↔
      M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0 := by
  exact
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.posteriorBernoulliMixture_processLawCrown_iff_zeroInteriorMixingMass
      M k l hZ

/-- Stable index-level alias for the proved infinite i.i.d. canonical compact
predictive/process-law regime split.  The canonical compact predictive endpoint
always exists, and the stronger raw process-law crown exists exactly in the
zero-interior-mixing regime. -/
theorem deFinetti_canonical_compactPredictiveThatsAll_and_processLawCrown_iff_zeroInteriorMixingMass
    (M : Mettapedia.Logic.DeFinetti.BernoulliMixture) (k l : ℕ)
    (hZ : M.countEvidenceMass k l ≠ 0) :
    let A : Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw (ℕ → Bool) :=
      Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw.ofProcess
        (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixtureCanonicalProcessMeasure
          (M.posteriorBernoulliMixture k l hZ))
        Mettapedia.CategoryTheory.coordProcess
        (by
          intro i
          exact measurable_pi_apply (a := i))
    Mettapedia.Logic.ConceptOntology.compactPredictiveThatsAll
      (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.externalPathLawBoundedMeasurableCompactCredalSet
        ({A} : Set (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw
          (ℕ → Bool)))) ∧
      (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.PosteriorBernoulliMixtureProcessLawCrown
        M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0) := by
  exact
    Mettapedia.Logic.ConceptOntology.posteriorBernoulliMixture_canonical_compactPredictiveThatsAll_and_processLawCrown_iff_zeroInteriorMixingMass
      M k l hZ

/-- Stable index-level alias for the public sigma-additive infinite i.i.d.
mixing-family package.  The canonical `Bool^ℕ` family attached to a Bernoulli-
mixture credal set computes exactly the same finite-prefix and compact
bounded-measurable PLN readouts as the analytic imprecise de Finetti family. -/
theorem deFinetti_canonical_external_mixing_family
    (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture)
    (hC : C.Nonempty) :
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiCanonicalExternalMixingFamily
      C hC := by
  exact
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.impreciseDeFinetti_canonicalExternalMixingFamily
      C hC

/-- Stable index-level alias for the abstract infinite i.i.d. de Finetti crown
package built from analytic prefix laws plus an explicit finite-window
realization inside a compact carrier. -/
theorem deFinetti_analytic_mixingFamily_processLawCrown_of_prefixFiniteWindowRealization
    (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture)
    (hC : C.Nonempty)
    [TopologicalSpace
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
        (ℕ → Bool))]
    (carrier :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet
        (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet.IsConvex
        carrier)
    (hClosed : ∀ n,
      IsClosed
        {P :
            Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
              (ℕ → Bool) |
          ((Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                hC).cylinders.marginalPrevision n P) ∈
            Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.dominatingPreciseCompletions
              ((Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                    C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                    hC).localLower n)})
    (hRealize :
      (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
          C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
          hC).jointPrevisionsRealizedInCarrier
        (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessFiniteJointWindowSystem
          C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
          hC)
        carrier) :
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
      C hC := by
  exact
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_prefixFiniteWindowRealization
      C hC carrier hCompact hCarrierConvex hClosed hRealize

/-- Stable index-level alias for the concrete infinite i.i.d. de Finetti crown
package obtained from any carrier containing the explicit tail-false
finite-window realizers. -/
theorem deFinetti_analytic_mixingFamily_processLawCrown_of_prefixTailFalseExtensionCarrierSubset
    (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture)
    (hC : C.Nonempty)
    [TopologicalSpace
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
        (ℕ → Bool))]
    (carrier :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet
        (ℕ → Bool))
    (hCompact : IsCompact carrier)
    (hCarrierConvex :
      Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet.IsConvex
        carrier)
    (hClosed : ∀ n,
      IsClosed
        {P :
            Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
              (ℕ → Bool) |
          ((Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                hC).cylinders.marginalPrevision n P) ∈
            Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.dominatingPreciseCompletions
              ((Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                    C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                    hC).localLower n)})
    (hSubset :
      Mettapedia.Logic.DeFinettiProjectiveCredalBridge.prefixTailFalseExtensionCarrier ⊆
        carrier) :
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
      C hC := by
  exact
      Mettapedia.Logic.DeFinettiProjectiveCredalBridge.impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_of_prefixTailFalseExtensionCarrierSubset
        C hC carrier hCompact hCarrierConvex hClosed hSubset

/-- Stable index-level alias for the sharp F2 i.i.d. de Finetti boundary: the
external mixing-family readout is unconditional, while the raw all-gambles
analytic crown is equivalent to exact lower-prevision compatibility. -/
theorem deFinetti_analytic_mixingFamily_sharpCompatibilityCrown
    (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture)
    (hC : C.Nonempty) :
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiCanonicalExternalMixingFamily
        C hC ∧
      (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC ↔
        ∃ L : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision (ℕ → Bool),
          (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
            C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
            hC).respectsLocalLower L) := by
  exact
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.impreciseDeFinetti_analyticMixingFamily_sharpCompatibilityCrown
      C hC

/-- Stable index-level alias for the closed S2 verdict: the analytic raw crown
does not imply pointwise zero-interior for every member of the credal family. -/
theorem deFinetti_analytic_mixingFamily_rawCrown_not_implies_pointwiseZeroInterior :
    ¬ (∀ (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture) (hC : C.Nonempty),
        Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC →
          Mettapedia.Logic.DeFinettiProjectiveCredalBridge.AnalyticMixingFamilyPointwiseZeroInterior C) := by
  exact
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.not_forall_impreciseDeFinetti_analyticMixingFamilyProcessLawCrown_imp_pointwiseZeroInterior_closed

/-- Stable index-level alias for the proved infinite MLN collapse theorem:
uniform Dobrushin small influence forces uniqueness of the infinite DLR
measure. -/
theorem infiniteMLN_paperUniformSmallTotalInfluence_implies_uniqueMeasure
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
      Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    M.PaperUniqueMeasure := by
  exact M.paperUniformSmallTotalInfluence_implies_paperUniqueMeasure hM

/-- Stable index-level alias for the first concrete infinite DLR/PLN contrast:
positive strict width on the reinforced line and Dobrushin collapse on the
zero-weight grid. -/
theorem infiniteMLN_reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast :
    Mettapedia.Logic.MarkovLogicInfinitePLNCrown.ConcreteDLRPLNContrast := by
  exact
    Mettapedia.Logic.MarkovLogicInfinitePLNCrown.reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast

/-- Stable index-level alias for the symmetric-grid Ising reduction crown: the
high-temperature collapse theorem is proved, and the reduction turns a
low-temperature Peierls input into plus/minus separation and a strict PLN
interval. That Peierls input is now supplied unconditionally by
`symmetricGridZeroField_originPLNStrictIntervalCrown_of_axisAnchoredContourCode_twentyFour`,
so the low-temperature strict-interval direction is itself proved, not merely
reduced. -/
theorem infiniteMLN_symmetricGridZeroField_originPhaseCoexistenceReductionCrown :
    Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample.SymmetricGridZeroFieldOriginPhaseCoexistenceReductionCrown := by
  exact
    Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample.symmetricGridZeroField_originPhaseCoexistenceReductionCrown

/-- Focused, paper-facing endpoint for the confidence-formula characterization.

This deliberately packages only the proved surface:

* finite DOF/forcing characterization;
* explicit typed-STV canaries showing the residual degrees of freedom;
* the finite singleton-posterior exact ITV collapse;
  * the infinite DLR/MLN specialization into width-complement ITVs, including
    the proved Dobrushin uniqueness theorem, a concrete strict-width-versus-
    collapse contrast, and the symmetric-grid phase-coexistence reduction crown
    (whose low-temperature Peierls input is now supplied, closing the
    strict-interval direction unconditionally);
  * the public sigma-additive imprecise de Finetti mixing-family object and the
    exact lower-prevision compatibility boundary for the analytic raw
    all-gambles process-law crown, plus conditional finite-window realization
    routes into that crown;
  * the proved i.i.d. de Finetti compact-predictive / process-law regime split.

  This profile does not itself bundle the low-temperature two-dimensional
  phase-separation theorem on the MLN/Ising side; that crown
  (`symmetricGridZeroField_originPLNStrictIntervalCrown_of_axisAnchoredContourCode_twentyFour`)
  is now proved unconditionally and lives in
  `MarkovLogicInfiniteSymmetricGridExample`. -/
structure ConfidenceCharacterizationEndpointProfile where
  formulaCharacterization : FormulaCharacterizationProfile
  typedSTVSameStrengthCanHaveDifferentConfidence :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 2 2)
    x.strength = y.strength ∧ x.confidence.display ≠ y.confidence.display
  typedSTVSameConfidenceCanHaveDifferentStrength :
    let χ := plnOddsCoordinate 1 (by norm_num)
    let x := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 1 1)
    let y := Mettapedia.Logic.PLNTruthTower.TypedSTV.fromCounts χ
      (Mettapedia.Logic.PLNTruthTower.BinaryCounts.ofNatCounts 2 0)
    x.confidence.display = y.confidence.display ∧ x.strength ≠ y.strength
  walleyWidthComplementForcesPLNOdds :
    ∀ (χ : EvidenceWeightCoordinate) (s : ℝ) (hs : 0 < s)
      (_hχ : WidthComplementCompatible χ s) {n : ℝ} (_hn : 0 ≤ n),
        χ.encode n = (plnOddsCoordinate s hs).encode n
  finiteCanonicalExactPredictiveITV :
    ∀ (M : Mettapedia.Logic.DeFinetti.BernoulliMixture) (k l n : ℕ)
      (hZ : M.countEvidenceMass k l ≠ 0)
      (G : Mettapedia.ProbabilityTheory.ImpreciseProbability.Gamble
        (Fin n → Bool))
      (hG : ∀ ω, G ω ∈ Set.Icc (0 : ℝ) 1),
      Mettapedia.Logic.ConceptOntology.compactPredictiveThatsAll
          (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.externalPathLawBoundedMeasurableCompactCredalSet
            ({Mettapedia.Logic.ConceptOntology.posteriorCanonicalExternalBoolProcessLaw M k l hZ} :
              Set (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw
                (ℕ → Bool)))) ∧
        (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).lower =
          Mettapedia.Logic.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G ∧
        (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).upper =
          Mettapedia.Logic.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G ∧
        (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).width = 0 ∧
        (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).credibility = 1 ∧
        (Mettapedia.Logic.ConceptOntology.posteriorPrefixTypedReadoutITV M k l n hZ G hG).midpoint =
          Mettapedia.Logic.ConceptOntology.posteriorPrefixReadoutPrevision M k l n hZ G
  infiniteMLNCredalBridge :
    Mettapedia.Logic.MarkovLogicInfiniteCredalBridge.InfiniteMLNCredalBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  infiniteDLRQueryOutcomeITV :
    Mettapedia.Logic.MarkovLogicPLNTruthBridge.DLRQueryOutcomePLNBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  infiniteProjectiveDeFinettiBridge :
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ProjectiveDeFinettiCredalBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  infiniteCanonicalExternalMixingFamily :
    ∀ (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture) (hC : C.Nonempty),
      Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiCanonicalExternalMixingFamily
        C hC
  infiniteAnalyticMixingFamilySharpCompatibility :
    ∀ (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture)
      (hC : C.Nonempty),
      Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiCanonicalExternalMixingFamily
          C hC ∧
        (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
            C hC ↔
          ∃ L : Mettapedia.ProbabilityTheory.ImpreciseProbability.LowerPrevision (ℕ → Bool),
            (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
              C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
              hC).respectsLocalLower L)
  infiniteAnalyticMixingFamilyRawCrownDoesNotForcePointwiseZeroInterior :
    ¬ (∀ (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture) (hC : C.Nonempty),
        Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC →
          Mettapedia.Logic.DeFinettiProjectiveCredalBridge.AnalyticMixingFamilyPointwiseZeroInterior C)
  infiniteAnalyticMixingFamilyProcessLawCrownOfPrefixFiniteWindowRealization :
    ∀ (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture)
      (hC : C.Nonempty)
      [TopologicalSpace
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
          (ℕ → Bool))]
      (carrier :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet
          (ℕ → Bool))
      (_hCompact : IsCompact carrier)
      (_hCarrierConvex :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet.IsConvex
          carrier)
      (_hClosed : ∀ n,
        IsClosed
          {P :
              Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
                (ℕ → Bool) |
            ((Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                  C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                  hC).cylinders.marginalPrevision n P) ∈
              Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.dominatingPreciseCompletions
                ((Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                      C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                      hC).localLower n)})
      (_hRealize :
        (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
            C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
            hC).jointPrevisionsRealizedInCarrier
          (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessFiniteJointWindowSystem
            C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
            hC)
          carrier),
        Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC
  infiniteAnalyticMixingFamilyProcessLawCrownOfPrefixTailFalseExtensionCarrierSubset :
    ∀ (C : Set Mettapedia.Logic.DeFinetti.BernoulliMixture)
      (hC : C.Nonempty)
      [TopologicalSpace
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
          (ℕ → Bool))]
      (carrier :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet
          (ℕ → Bool))
      (_hCompact : IsCompact carrier)
      (_hCarrierConvex :
        Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.CredalPrevisionSet.IsConvex
          carrier)
      (_hClosed : ∀ n,
        IsClosed
          {P :
              Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision
                (ℕ → Bool) |
            ((Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                  C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                  hC).cylinders.marginalPrevision n P) ∈
              Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.dominatingPreciseCompletions
                ((Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixProcessLowerSpec
                      C (fun M _ n => Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixturePrefixLaw_analytic M n)
                      hC).localLower n)})
      (_hSubset :
        Mettapedia.Logic.DeFinettiProjectiveCredalBridge.prefixTailFalseExtensionCarrier ⊆
          carrier),
        Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ImpreciseDeFinettiAnalyticMixingFamilyProcessLawCrown
          C hC
  infiniteProcessLawCrownBoundary :
    ∀ (M : Mettapedia.Logic.DeFinetti.BernoulliMixture) (k l : ℕ)
      (hZ : M.countEvidenceMass k l ≠ 0),
      Mettapedia.Logic.DeFinettiProjectiveCredalBridge.PosteriorBernoulliMixtureProcessLawCrown
        M k l hZ ↔
        M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0
  infiniteCanonicalCompactPredictiveProcessLawBoundary :
    ∀ (M : Mettapedia.Logic.DeFinetti.BernoulliMixture) (k l : ℕ)
      (hZ : M.countEvidenceMass k l ≠ 0),
      let A : Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw (ℕ → Bool) :=
        Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw.ofProcess
          (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.bernoulliMixtureCanonicalProcessMeasure
            (M.posteriorBernoulliMixture k l hZ))
          Mettapedia.CategoryTheory.coordProcess
          (by
            intro i
            exact measurable_pi_apply (a := i))
      Mettapedia.Logic.ConceptOntology.compactPredictiveThatsAll
        (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.externalPathLawBoundedMeasurableCompactCredalSet
          ({A} : Set (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ExternalBoolProcessLaw
            (ℕ → Bool)))) ∧
        (Mettapedia.Logic.DeFinettiProjectiveCredalBridge.PosteriorBernoulliMixtureProcessLawCrown
          M k l hZ ↔
          M.mixingMeasure (Set.Ioo (0 : ℝ) 1) = 0)
  infiniteDobrushinUniqueness :
    ∀ {Atom ClauseId : Type} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
        Atom ClauseId),
      M.PaperUniformSmallTotalInfluence →
        M.PaperUniqueMeasure
  infiniteConcreteStrictWidthVsCollapseContrast :
    Mettapedia.Logic.MarkovLogicInfinitePLNCrown.ConcreteDLRPLNContrast
  infiniteSymmetricGridPhaseCoexistenceReduction :
    Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample.SymmetricGridZeroFieldOriginPhaseCoexistenceReductionCrown

/-- Current focused endpoint for the confidence-formula characterization. -/
noncomputable def confidenceCharacterizationEndpointProfile :
    ConfidenceCharacterizationEndpointProfile where
  formulaCharacterization :=
    formulaCharacterizationProfile
  typedSTVSameStrengthCanHaveDifferentConfidence :=
    typed_stv_same_strength_can_have_different_confidence
  typedSTVSameConfidenceCanHaveDifferentStrength :=
    typed_stv_same_confidence_can_have_different_strength
  walleyWidthComplementForcesPLNOdds :=
    walley_width_complement_forces_pln_odds
  finiteCanonicalExactPredictiveITV :=
    deFinetti_canonical_compactPredictiveThatsAll_and_prefixTypedWidthComplementITV_exact
  infiniteMLNCredalBridge :=
    Mettapedia.Logic.MarkovLogicInfiniteCredalBridge.infiniteMLNCredalBridgeProfile
  infiniteDLRQueryOutcomeITV :=
    Mettapedia.Logic.MarkovLogicPLNTruthBridge.dlrQueryOutcomePLNBridgeProfile
  infiniteProjectiveDeFinettiBridge :=
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.projectiveDeFinettiCredalBridgeProfile
  infiniteCanonicalExternalMixingFamily :=
    deFinetti_canonical_external_mixing_family
  infiniteAnalyticMixingFamilySharpCompatibility :=
    deFinetti_analytic_mixingFamily_sharpCompatibilityCrown
  infiniteAnalyticMixingFamilyRawCrownDoesNotForcePointwiseZeroInterior :=
    deFinetti_analytic_mixingFamily_rawCrown_not_implies_pointwiseZeroInterior
  infiniteAnalyticMixingFamilyProcessLawCrownOfPrefixFiniteWindowRealization :=
    deFinetti_analytic_mixingFamily_processLawCrown_of_prefixFiniteWindowRealization
  infiniteAnalyticMixingFamilyProcessLawCrownOfPrefixTailFalseExtensionCarrierSubset :=
    deFinetti_analytic_mixingFamily_processLawCrown_of_prefixTailFalseExtensionCarrierSubset
  infiniteProcessLawCrownBoundary :=
    deFinetti_posterior_processLawCrown_iff_zeroInteriorMixingMass
  infiniteCanonicalCompactPredictiveProcessLawBoundary :=
    deFinetti_canonical_compactPredictiveThatsAll_and_processLawCrown_iff_zeroInteriorMixingMass
  infiniteDobrushinUniqueness :=
    infiniteMLN_paperUniformSmallTotalInfluence_implies_uniqueMeasure
  infiniteConcreteStrictWidthVsCollapseContrast :=
    infiniteMLN_reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast
  infiniteSymmetricGridPhaseCoexistenceReduction :=
    infiniteMLN_symmetricGridZeroField_originPhaseCoexistenceReductionCrown

/-- External runtime parity metadata for the arithmetic/provenance mirror.
This is not a proof object; the corresponding commands are run by the build
agent. -/
structure RuntimeParitySurface where
  projectionTowerPeTTaPath : String
  projectionTowerCeTTaPath : String
  projectionTowerExpectedChecks : Nat
  itvIDMPeTTaPath : String
  itvIDMCeTTaPath : String
  itvIDMExpectedChecks : Nat
  truthFunctionPeTTaPath : String
  truthFunctionCeTTaPath : String
  truthFunctionExpectedChecks : Nat
  strengthPriorPeTTaPath : String
  strengthPriorCeTTaPath : String
  strengthPriorExpectedChecks : Nat

/-- Current PeTTa/CeTTa parity surface for the projection-tower canary,
ITV/IDM arithmetic, typed bridge/provenance mirrors, PeTTa truth-function
confidence audit, and strength-prior canaries. -/
def plnITVIDMRuntimeParitySurface : RuntimeParitySurface where
  projectionTowerPeTTaPath :=
    "/home/zar/claude/hyperon/PeTTa/examples/pln_projection_tower_bool_canary.metta"
  projectionTowerCeTTaPath :=
    "/home/zar/claude/hyperon/CeTTa/tests/test_wmpln_projection_tower_bool_canary.metta"
  projectionTowerExpectedChecks := 15
  itvIDMPeTTaPath :=
    "/home/zar/claude/hyperon/PeTTa/examples/pln_itv_idm_parity_golden.metta"
  itvIDMCeTTaPath :=
    "/home/zar/claude/hyperon/CeTTa/tests/test_wmpln_itv_idm_parity_golden.metta"
  itvIDMExpectedChecks := 26
  truthFunctionPeTTaPath :=
    "/home/zar/claude/hyperon/PeTTa/examples/pln_truth_parity_golden.metta"
  truthFunctionCeTTaPath :=
    "/home/zar/claude/hyperon/CeTTa/tests/test_wmpln_truth_parity_golden.metta"
  truthFunctionExpectedChecks := 11
  strengthPriorPeTTaPath :=
    "/home/zar/claude/hyperon/PeTTa/examples/pln_strength_prior_canary.metta"
  strengthPriorCeTTaPath :=
    "/home/zar/claude/hyperon/CeTTa/tests/test_wmpln_strength_prior_canary.metta"
  strengthPriorExpectedChecks := 13

/-! ## Whole truth-theory package -/

/-- Top-level package for the current confidence / strength / ITV theory
surface.  The fields are theorem-profile values, so importing this package
gives a compact proof-carrying index of the current formal story. -/
structure TruthTheoryPackage where
  confidenceCharacterizationEndpoint : ConfidenceCharacterizationEndpointProfile
  confidenceFormulaAudit : ConfidenceFormulaAuditProfile
  confidenceChartTorsor : ConfidenceChartTorsorProfile
  confidenceRevisionCharts : ConfidenceRevisionChartProfile
  genericITV : GenericITVProfile
  bayesCredible : BayesCredibleProfile
  walleyBinary : WalleyBinaryProfile
  walleyCategorical : WalleyCategoricalProfile
  strengthProjection : StrengthProjectionProfile
  meanConcentration : MeanConcentrationProfile
  informationGeometry : InformationGeometryLiftProfile
  amplitudePhase : AmplitudePhasePLNProfile
  sufficientStatisticQueries : SufficientStatisticQueryProfile
  typedITVOperations : TypedITVOperationProfile
  worldModelTypedITVs : WorldModelTypedITVProfile
  credalForcedQueries : CredalForcedQueryProfile
  credalProjectionTower : CredalProjectionTowerProfile
  naturalExtension : NaturalExtensionProfile
  projectiveCredal : Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.ProjectiveCredalProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  infiniteMLNCredalBridge : Mettapedia.Logic.MarkovLogicInfiniteCredalBridge.InfiniteMLNCredalBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  dlrQueryOutcomePLNBridge : Mettapedia.Logic.MarkovLogicPLNTruthBridge.DLRQueryOutcomePLNBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  projectiveDeFinettiCredalBridge : Mettapedia.Logic.DeFinettiProjectiveCredalBridge.ProjectiveDeFinettiCredalBridgeProfile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  coreFourCompletion : CoreFourCompletionProfile
  crispnessCollapse : CrispnessCollapseProfile
  degreesOfFreedomForcing : DegreesOfFreedomForcingProfile
  formulaCharacterization : FormulaCharacterizationProfile
  paperFacingSynthesis : PaperFacingDOFForcingSynthesisProfile
  didacticWitnesses : Mettapedia.Logic.PLNDidacticWitnesses.DidacticWitnessProfile
  runtimeParity : RuntimeParitySurface

/-- The current proof-carrying package for the confidence / strength / ITV
theory surface. -/
noncomputable def plnTruthTheoryPackage : TruthTheoryPackage where
  confidenceCharacterizationEndpoint :=
    confidenceCharacterizationEndpointProfile
  confidenceFormulaAudit := confidenceFormulaAuditProfile
  confidenceChartTorsor := confidenceChartTorsorProfile
  confidenceRevisionCharts := confidenceRevisionChartProfile
  genericITV := genericITVProfile
  bayesCredible := bayesCredibleProfile
  walleyBinary := walleyBinaryProfile
  walleyCategorical := walleyCategoricalProfile
  strengthProjection := strengthProjectionProfile
  meanConcentration := meanConcentrationProfile
  informationGeometry := informationGeometryLiftProfile
  amplitudePhase := amplitudePhasePLNProfile
  sufficientStatisticQueries := sufficientStatisticQueryProfile
  typedITVOperations := typedITVOperationProfile
  worldModelTypedITVs := worldModelTypedITVProfile
  credalForcedQueries := credalForcedQueryProfile
  credalProjectionTower := credalProjectionTowerProfile
  naturalExtension := naturalExtensionProfile
  projectiveCredal :=
    Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.projectiveCredalProfile
  infiniteMLNCredalBridge :=
    Mettapedia.Logic.MarkovLogicInfiniteCredalBridge.infiniteMLNCredalBridgeProfile
  dlrQueryOutcomePLNBridge :=
    Mettapedia.Logic.MarkovLogicPLNTruthBridge.dlrQueryOutcomePLNBridgeProfile
  projectiveDeFinettiCredalBridge :=
    Mettapedia.Logic.DeFinettiProjectiveCredalBridge.projectiveDeFinettiCredalBridgeProfile
  coreFourCompletion := coreFourCompletionProfile
  crispnessCollapse := crispnessCollapseProfile
  degreesOfFreedomForcing := degreesOfFreedomForcingProfile
  formulaCharacterization := formulaCharacterizationProfile
  paperFacingSynthesis := paperFacingDOFForcingSynthesisProfile
  didacticWitnesses := Mettapedia.Logic.PLNDidacticWitnesses.didacticWitnessProfile
  runtimeParity := plnITVIDMRuntimeParitySurface

end Mettapedia.Logic.PLNTruthTheoryIndex
