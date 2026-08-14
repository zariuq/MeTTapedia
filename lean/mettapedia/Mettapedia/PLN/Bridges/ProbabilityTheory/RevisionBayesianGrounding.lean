import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
import Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevisionProfile

/-!
# Revision Bayesian Grounding Profile

This file packages the existing theorem family connecting finite PLN Revision
to Beta-Bernoulli sufficient-statistic updating.

It is intentionally a bridge profile: the rule-family algebra stays in
`PLNRevisionProfile`, while the Bayesian / de-Finetti scope and the
exchangeable-not-Beta guardrail stay in the probability bridge layer.
-/

namespace Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionBayesianGrounding

open scoped ENNReal
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
open Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge

/-- Reader-facing theorem profile for the Bayesian grounding of finite
binary-evidence Revision.

The positive fields connect raw finite-source Revision to the Beta-Bernoulli
sufficient-statistic update.  The negative fields record the honest boundary:
exchangeability gives count-based de-Finetti mixture predictors, but does not
force the Beta posterior-predictive subfamily. -/
structure RevisionBayesianGroundingProfile where
  finiteRuleFamily : RevisionRuleFamilyProfile
  conjugateUpdate :
    ∀ (prior_param : ℝ) (hprior : 0 < prior_param)
      (n₁_pos n₁_neg n₂_pos n₂_neg : ℕ),
      let params₁ :=
        { prior_param := prior_param, prior_pos := hprior,
          evidence_pos := n₁_pos, evidence_neg := n₁_neg : EvidenceBetaParams }
      let params_combined :=
        { prior_param := prior_param, prior_pos := hprior,
          evidence_pos := n₁_pos + n₂_pos,
          evidence_neg := n₁_neg + n₂_neg : EvidenceBetaParams }
      params_combined.alpha = params₁.alpha + n₂_pos ∧
        params_combined.beta = params₁.beta + n₂_neg
  hplusSufficientStatistics :
    ∀ e₁ e₂ : BinaryEvidence,
      (e₁ + e₂).pos = e₁.pos + e₂.pos ∧
        (e₁ + e₂).neg = e₁.neg + e₂.neg
  finiteBatchSufficientStatistics :
    ∀ (prior_param : ℝ) (hprior : 0 < prior_param) (xs : List (ℕ × ℕ)),
      (revisionMany (xs.map countPairEvidence)).pos =
          (xs.map (fun nm => (nm.1 : ℝ≥0∞))).sum ∧
        (revisionMany (xs.map countPairEvidence)).neg =
          (xs.map (fun nm => (nm.2 : ℝ≥0∞))).sum ∧
      (batchEvidenceBetaParams prior_param hprior xs).alpha =
        prior_param + (xs.map Prod.fst).sum ∧
      (batchEvidenceBetaParams prior_param hprior xs).beta =
        prior_param + (xs.map Prod.snd).sum
  guardedFiniteBatchSufficientStatistics :
    ∀ {Stamp : Type} [DecidableEq Stamp]
      (prior_param : ℝ) (hprior : 0 < prior_param)
      (xs : List (Finset Stamp × (ℕ × ℕ))),
      (countPairStampedBatch (Stamp := Stamp) xs).Pairwise
          StampedBinaryEvidence.StampDisjoint →
        guardedRevisionManyEvidence (countPairStampedBatch (Stamp := Stamp) xs) =
            some (revisionMany ((countPairLedger xs).map countPairEvidence)) ∧
          (revisionMany ((countPairLedger xs).map countPairEvidence)).pos =
              ((countPairLedger xs).map (fun nm => (nm.1 : ENNReal))).sum ∧
            (revisionMany ((countPairLedger xs).map countPairEvidence)).neg =
              ((countPairLedger xs).map (fun nm => (nm.2 : ENNReal))).sum ∧
            (batchEvidenceBetaParams prior_param hprior (countPairLedger xs)).alpha =
              prior_param + ((countPairLedger xs).map Prod.fst).sum ∧
            (batchEvidenceBetaParams prior_param hprior (countPairLedger xs)).beta =
              prior_param + ((countPairLedger xs).map Prod.snd).sum
  finiteBatchOrderInvariant :
    ∀ (prior_param : ℝ) (hprior : 0 < prior_param)
      {xs ys : List (ℕ × ℕ)}, xs.Perm ys →
      revisionMany (xs.map countPairEvidence) =
          revisionMany (ys.map countPairEvidence) ∧
        batchEvidenceBetaParams prior_param hprior xs =
          batchEvidenceBetaParams prior_param hprior ys
  laplacePosteriorMeanReadout :
    ∀ xs : List (ℕ × ℕ),
      (revisionMany (xs.map countPairEvidence)).pos =
          (xs.map (fun nm => (nm.1 : ℝ≥0∞))).sum ∧
        (revisionMany (xs.map countPairEvidence)).neg =
          (xs.map (fun nm => (nm.2 : ℝ≥0∞))).sum ∧
        (batchEvidenceBetaParams 1 (by norm_num : 0 < (1 : ℝ)) xs).posteriorMean =
          uniformPosteriorMean (xs.map Prod.fst).sum (xs.map Prod.snd).sum
  laplaceBetaBernoulliPredictive :
    ∀ xs : List (ℕ × ℕ),
      (revisionMany (xs.map countPairEvidence)).pos =
          (xs.map (fun nm => (nm.1 : ℝ≥0∞))).sum ∧
        (revisionMany (xs.map countPairEvidence)).neg =
          (xs.map (fun nm => (nm.2 : ℝ≥0∞))).sum ∧
        ((batchEvidenceBetaParams 1 (by norm_num : 0 < (1 : ℝ)) xs).toBetaPrior).mean =
          uniformPosteriorMean (xs.map Prod.fst).sum (xs.map Prod.snd).sum
  exchangeableMixtureValues :
    twoPointExchangeableMixturePredictorN2 0 = (15 / 44 : ℝ) ∧
      twoPointExchangeableMixturePredictorN2 1 = (7 / 12 : ℝ) ∧
      twoPointExchangeableMixturePredictorN2 2 = (55 / 76 : ℝ)
  exchangeableMixtureViolatesBetaAffine :
    (2 : ℝ) * twoPointExchangeableMixturePredictorN2 1 ≠
      twoPointExchangeableMixturePredictorN2 0 +
        twoPointExchangeableMixturePredictorN2 2
  exchangeableNotBetaBoundary :
    ¬ ∃ α β : ℝ,
      twoPointExchangeableMixturePredictorN2 0 = (α / (2 + α + β)) ∧
      twoPointExchangeableMixturePredictorN2 1 = ((1 + α) / (2 + α + β)) ∧
      twoPointExchangeableMixturePredictorN2 2 = ((2 + α) / (2 + α + β))

/-- Compact public handle for finite Revision's Bayesian grounding. -/
noncomputable def revisionBayesianGroundingProfile :
    RevisionBayesianGroundingProfile where
  finiteRuleFamily := revisionRuleFamilyProfile
  conjugateUpdate := evidence_aggregation_is_conjugate_update
  hplusSufficientStatistics := hplus_is_beta_aggregation
  finiteBatchSufficientStatistics :=
    revisionMany_countPairEvidence_is_beta_batch_update
  guardedFiniteBatchSufficientStatistics :=
    guardedRevisionManyCountPairEvidence_is_beta_batch_update_of_pairwise
  finiteBatchOrderInvariant :=
    revisionMany_countPairEvidence_beta_batch_update_perm
  laplacePosteriorMeanReadout :=
    revisionMany_countPairEvidence_laplace_posteriorMean
  laplaceBetaBernoulliPredictive :=
    revisionMany_countPairEvidence_laplace_betaBernoulliPredictive
  exchangeableMixtureValues :=
    twoPointExchangeableMixturePredictorN2_eval
  exchangeableMixtureViolatesBetaAffine :=
    twoPointExchangeableMixturePredictorN2_violates_beta_affine
  exchangeableNotBetaBoundary :=
    twoPointExchangeableMixturePredictorN2_not_beta

end Mettapedia.PLN.Bridges.ProbabilityTheory.RevisionBayesianGrounding
