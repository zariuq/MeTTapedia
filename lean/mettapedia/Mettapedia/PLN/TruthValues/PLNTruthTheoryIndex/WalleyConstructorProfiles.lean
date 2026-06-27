import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex.InformationRevisionSubjective

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
    {k : ℕ} (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
    (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k)
    (i j : Fin k) (hji : j ≠ i) :
    Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.categoryGamble i) =
          Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmLower ctx e i ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.categoryGamble i) =
          Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmUpper ctx e i ∧
      Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.upperProb
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.categoryGamble i) -
        Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles.lowerProb
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.credalSet e ctx.s ctx.s_pos)
          (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyMultinomialIDM.categoryGamble i) =
            Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.idmWidth ctx e :=
  walleyMultinomial_category_envelope_matches_EvidenceDirichlet ctx e i j hji

/-- For a symmetric Dirichlet prior, the posterior blend weight is exactly the
PLN odds confidence link applied to categorical concentration, with the link
scale set to the prior concentration. -/
theorem symmetric_dirichlet_blend_weight_is_concentration_link
    {k : ℕ} (π : SymmetricDirichletPrior k) (hk : 0 < k)
    (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k) :
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
    (e : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.MultiEvidence k)
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
    ∀ (a b c ba bc : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthInduction
        a b c ba bc).c =
        Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
          (min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w ba.c)
            (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w bc.c))
  abductionConfidenceWeightMin :
    ∀ (a b c ab cb : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthAbduction
        a b c ab cb).c =
        Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
          (min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w ab.c)
            (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w cb.c))
  weightMinCollapsesToMinCappedConfidence :
    ∀ c₁ c₂ : ℝ,
      Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
          (min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w c₁)
            (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w c₂)) =
        min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf c₁)
          (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf c₂)
  revisionConfidenceWeightAddition :
    ∀ (t₁ t₂ : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthRevision t₁ t₂).c =
        min 1 (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.w2c
          (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w t₁.c +
            Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.c2w t₂.c))
  negationPreservesConfidence :
    ∀ (t : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthNegation t).c = t.c
  modusPonensConfidenceProduct :
    ∀ (p pq : Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.TV),
      (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens p pq).c =
        p.c * pq.c
  modusPonensProductBelowMinCanary :
    (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.truthModusPonens
        ⟨0, 0.5⟩ ⟨0, 0.5⟩).c <
      min (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf 0.5)
        (Mettapedia.PLN.TruthValues.PeTTaLibPLNTruthFunctions.capConf 0.5)

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


end Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex
