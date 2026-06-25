import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
import Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore

/-!
# Subjective-Logic Coordinates for the Evidence/Beta PLN Core

This file records the narrow bridge we need from binomial Subjective Logic into
the already-formalized PLN evidence layer.  A binomial opinion with base rate
`1/2` and evidence counts `(r, s)` has projected probability
`b + a * u = (r + 1) / (r + s + 2)`, i.e. the Laplace/Beta posterior mean.

The bridge is intentionally one-way as an integration surface: Subjective Logic
is a coordinate presentation of the EvidenceBeta/Revision core, not a second
truth-value semantics.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
open Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore

/-- Minimal binomial-opinion record: belief, disbelief, uncertainty, base rate. -/
structure BinomialOpinion where
  belief : ℝ
  disbelief : ℝ
  uncertainty : ℝ
  baseRate : ℝ

namespace BinomialOpinion

/-- Projected probability of a binomial opinion. -/
noncomputable def projected (o : BinomialOpinion) : ℝ :=
  o.belief + o.baseRate * o.uncertainty

end BinomialOpinion

/-- The binomial Subjective-Logic opinion induced by counts and base rate `1/2`.

The denominator includes the two symmetric prior pseudo-counts. -/
noncomputable def laplaceOpinion (nPos nNeg : ℕ) : BinomialOpinion where
  belief := (nPos : ℝ) / ((nPos : ℝ) + (nNeg : ℝ) + 2)
  disbelief := (nNeg : ℝ) / ((nPos : ℝ) + (nNeg : ℝ) + 2)
  uncertainty := 2 / ((nPos : ℝ) + (nNeg : ℝ) + 2)
  baseRate := 1 / 2

/-! ## General base-rate dictionary

Subjective Logic's base rate is not an extra PLN semantics.  It is the prior
mean of an ordinary Beta prior, with total prior weight split as
`a * W` positive pseudo-counts and `(1 - a) * W` negative pseudo-counts.
The uniform/Laplace bridge above is the special case `a = 1/2`, `W = 2`.
-/

/-- Binomial Subjective-Logic opinion induced by real-valued evidence counts,
base rate `a`, and total prior weight `W`.

For the intended probability reading use `0 ≤ a ≤ 1` and `0 < W`.  The algebraic
projection theorem below is stated separately from those side conditions so it
can be reused as a coordinate identity. -/
noncomputable def weightedOpinion (nPos nNeg : ℝ) (baseRate priorWeight : ℝ) :
    BinomialOpinion where
  belief := nPos / (nPos + nNeg + priorWeight)
  disbelief := nNeg / (nPos + nNeg + priorWeight)
  uncertainty := priorWeight / (nPos + nNeg + priorWeight)
  baseRate := baseRate

/-- The asymmetric Beta posterior mean corresponding to Subjective Logic base
rate `a` and total prior weight `W`: prior positive mass `aW`, negative mass
`(1-a)W`, then evidence `(n⁺, n⁻)`. -/
noncomputable def asymmetricBetaPosteriorMean
    (nPos nNeg : ℝ) (baseRate priorWeight : ℝ) : ℝ :=
  (nPos + baseRate * priorWeight) / (nPos + nNeg + priorWeight)

/-- Weighted Subjective-Logic mass components sum to one when the denominator is
positive. -/
theorem weightedOpinion_mass_eq_one
    {nPos nNeg baseRate priorWeight : ℝ}
    (hPos : 0 ≤ nPos) (hNeg : 0 ≤ nNeg) (hW : 0 < priorWeight) :
    (weightedOpinion nPos nNeg baseRate priorWeight).belief +
        (weightedOpinion nPos nNeg baseRate priorWeight).disbelief +
        (weightedOpinion nPos nNeg baseRate priorWeight).uncertainty = 1 := by
  unfold weightedOpinion
  have hden : nPos + nNeg + priorWeight ≠ 0 := by
    nlinarith
  field_simp [hden]

/-- Subjective-Logic projected probability is exactly the corresponding
asymmetric Beta posterior mean.

This is the small but load-bearing dictionary theorem: SL's `(b,d,u,a)`
coordinates and the EvidenceBeta/de-Finetti posterior mean are the same
evidential object in different coordinates. -/
theorem weightedOpinion_projected_eq_asymmetricBetaPosteriorMean
    (nPos nNeg baseRate priorWeight : ℝ) :
    (weightedOpinion nPos nNeg baseRate priorWeight).projected =
      asymmetricBetaPosteriorMean nPos nNeg baseRate priorWeight := by
  unfold BinomialOpinion.projected weightedOpinion asymmetricBetaPosteriorMean
  ring_nf

/-- The Laplace/uniform bridge is the base-rate `1/2`, prior-weight `2` special
case of the general weighted Subjective-Logic dictionary. -/
theorem weightedOpinion_uniform_projected_eq_laplaceOpinion
    (nPos nNeg : ℕ) :
    (weightedOpinion (nPos : ℝ) (nNeg : ℝ) (1 / 2 : ℝ) 2).projected =
      (laplaceOpinion nPos nNeg).projected := by
  rw [weightedOpinion_projected_eq_asymmetricBetaPosteriorMean]
  unfold asymmetricBetaPosteriorMean BinomialOpinion.projected laplaceOpinion
  ring_nf

/-- The binomial-opinion mass components sum to one. -/
theorem laplaceOpinion_mass_eq_one (nPos nNeg : ℕ) :
    (laplaceOpinion nPos nNeg).belief +
        (laplaceOpinion nPos nNeg).disbelief +
        (laplaceOpinion nPos nNeg).uncertainty = 1 := by
  unfold laplaceOpinion
  have hden : ((nPos : ℝ) + (nNeg : ℝ) + 2) ≠ 0 := by positivity
  field_simp [hden]

/-- Subjective-Logic projection is exactly the Laplace/Beta posterior mean. -/
theorem laplaceOpinion_projected_eq_uniformPosteriorMean
    (nPos nNeg : ℕ) :
    (laplaceOpinion nPos nNeg).projected =
      Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.uniformPosteriorMean nPos nNeg := by
  unfold BinomialOpinion.projected laplaceOpinion uniformPosteriorMean
  simp [Mettapedia.PLN.Evidence.EvidenceCounts.uniformPosteriorMean]
  ring_nf

/-- Same dictionary theorem stated against the `EvidenceBetaParams` surface. -/
theorem laplaceOpinion_projected_eq_EvidenceBetaParams_posteriorMean
    (nPos nNeg : ℕ) :
    (laplaceOpinion nPos nNeg).projected =
      (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.withUniformPrior nPos nNeg).posteriorMean := by
  unfold BinomialOpinion.projected laplaceOpinion
  unfold EvidenceBetaParams.posteriorMean EvidenceBetaParams.alpha
    EvidenceBetaParams.beta withUniformPrior
  ring_nf

/-! ## Raw evidence fusion, before projection -/

/-- Raw Subjective-Logic evidence fusion is evidence addition before projection.

This is the positive side of the dictionary: to use Subjective-Logic
coordinates as the EvidenceBeta/Revision core, combine the sufficient
statistics first and then read out the projected probability. -/
theorem laplaceOpinion_projected_rawEvidenceAdd_eq_EvidenceBetaParams_posteriorMean
    (n₁Pos n₁Neg n₂Pos n₂Neg : ℕ) :
    (laplaceOpinion (n₁Pos + n₂Pos) (n₁Neg + n₂Neg)).projected =
      (Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta.withUniformPrior
        (n₁Pos + n₂Pos) (n₁Neg + n₂Neg)).posteriorMean :=
  laplaceOpinion_projected_eq_EvidenceBetaParams_posteriorMean
    (n₁Pos + n₂Pos) (n₁Neg + n₂Neg)

/-- MeTTa-facing raw count Revision is exactly finite evidence-count addition.

The theorem is restated here as part of the SL dictionary because it is the
operational guardrail: Revision is sound at the raw-evidence layer.  It should
not be read as permission to revise already-prior-loaded projected
probabilities. -/
theorem semanticPLNRevision_rawCountSTV_eq_added_count_view
    (e₁ e₂ : Mettapedia.PLN.TruthValues.PLNTruthTower.BinaryCounts)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0) :
    let tv₁ := semanticPLNCountSTV e₁ h₁
    let tv₂ := semanticPLNCountSTV e₂ h₂
    (semanticPLNRevision tv₁ tv₂).strength = (e₁.add e₂).strength ∧
      (semanticPLNRevision tv₁ tv₂).confidence =
        semanticPLNOddsCoordinate.encode ((e₁.add e₂).total) :=
  semanticPLNRevision_countSTV_eq_added_count_view e₁ e₂ h₁ h₂
    (ne_of_gt (add_pos (e₁.total_pos_of_ne_zero h₁) (e₂.total_pos_of_ne_zero h₂)))

/-! ## Prior-loaded readout guardrail

Revision is sound at the raw-evidence/sufficient-statistic layer.  If each
source is first projected with its own symmetric prior and then the displayed
STVs are revised, the shared prior is counted more than once.  The canary below
keeps that boundary theorem-visible.
-/

/-- Prior-loaded projected readout for `(6,0)` evidence:
`(6 + 1) / (6 + 0 + 2) = 7/8`, confidence `6/(6+1)`. -/
noncomputable def priorLoadedProjectionSTV_6_0 : STV where
  strength := (7 / 8 : ℝ)
  confidence := (6 / 7 : ℝ)
  strength_nonneg := by norm_num
  strength_le_one := by norm_num
  confidence_nonneg := by norm_num
  confidence_le_one := by norm_num

/-- Prior-loaded projected readout for `(0,2)` evidence:
`(0 + 1) / (0 + 2 + 2) = 1/4`, confidence `2/(2+1)`. -/
noncomputable def priorLoadedProjectionSTV_0_2 : STV where
  strength := (1 / 4 : ℝ)
  confidence := (2 / 3 : ℝ)
  strength_nonneg := by norm_num
  strength_le_one := by norm_num
  confidence_nonneg := by norm_num
  confidence_le_one := by norm_num

/-- Revising prior-loaded projected readouts produces the weighted-readout value
`23/32`.  This is not the shared-prior Beta posterior mean. -/
theorem semanticPLNRevision_priorLoadedProjection_strength_eq :
    (semanticPLNRevision priorLoadedProjectionSTV_6_0
        priorLoadedProjectionSTV_0_2).strength = (23 / 32 : ℝ) := by
  norm_num [semanticPLNRevision, Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceCalculus.revisionTV,
    Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceCalculus.c2w, Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.clamp01,
    priorLoadedProjectionSTV_6_0, priorLoadedProjectionSTV_0_2]

/-- The corresponding shared-prior update over combined raw evidence is `7/10`. -/
theorem sharedPriorCombinedProjection_6_2_eq :
    (laplaceOpinion 6 2).projected = (7 / 10 : ℝ) := by
  norm_num [BinomialOpinion.projected, laplaceOpinion]

/-- Guardrail: do not treat revision of two prior-loaded projections as the same
operation as one shared-prior update over the combined evidence. -/
theorem semanticPLNRevision_priorLoadedProjection_ne_sharedPrior :
    (semanticPLNRevision priorLoadedProjectionSTV_6_0
        priorLoadedProjectionSTV_0_2).strength ≠ (laplaceOpinion 6 2).projected := by
  rw [semanticPLNRevision_priorLoadedProjection_strength_eq,
    sharedPriorCombinedProjection_6_2_eq]
  norm_num

end Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge
