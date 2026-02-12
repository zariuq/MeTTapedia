import Mettapedia.Logic.PremiseSelectionOperatorRoles
import Mettapedia.Logic.PremiseSelectionOptimality

/-!
# Concrete Prior-NB Premise-Selection Theorems

This module instantiates the operator-role layer with the concrete Prior-NB structure:

- `globalPrior` and `localPrior` are pooled by revision (`fuse` / `hplus`)
- pooled prior is updated by feature-likelihood (`update` / tensor)

It provides theorem statements directly aligned with the current selector semantics.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical ENNReal
open Mettapedia.Logic.PremiseSelectionOptimality
open Mettapedia.Logic.EvidenceQuantale

variable {Goal Fact : Type*}

/-- Assumption checklist for the finite, local-exchangeable, top-k surrogate regime
used by Prior-NB premise selection.

This checklist is intentionally minimal and task-facing:
- finite premise pool (`Fact`)
- local exchangeability within bins of goals
- explicit top-k budget bounded by pool size
- coverage-style surrogate objective for theorem-level ranking analysis
-/
structure PriorNBAssumptionChecklist (Goal Fact Bin : Type*) [Fintype Fact] where
  inBin : Goal → Bin
  finitePool_nonempty : 0 < Fintype.card Fact
  localExchangeabilityInBin : Prop
  topK : ℕ
  topK_pos : 0 < topK
  topK_le_pool : topK ≤ Fintype.card Fact
  surrogateCoverageObjective : Prop

/-- Prior-NB posterior: pooled priors updated by likelihood evidence. -/
noncomputable def priorNBPosterior
    (globalPrior localPrior likelihood : Scorer Goal Fact) : Scorer Goal Fact :=
  update (fuse globalPrior localPrior) likelihood

/-- Equivalent two-stage Prior-NB form: update each prior, then pool. -/
noncomputable def priorNBPosteriorTwoStage
    (globalPrior localPrior likelihood : Scorer Goal Fact) : Scorer Goal Fact :=
  fuse (update globalPrior likelihood) (update localPrior likelihood)

theorem priorNBPosterior_eq_twoStage
    (globalPrior localPrior likelihood : Scorer Goal Fact) :
    priorNBPosterior globalPrior localPrior likelihood =
      priorNBPosteriorTwoStage globalPrior localPrior likelihood := by
  simp [priorNBPosterior, priorNBPosteriorTwoStage, externalBayesianity_hplus_tensor]

theorem priorNBPosterior_isPosterior
    (T : OperatorRoleTheory Goal Fact)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (hGlobalPrior : T.IsPrior globalPrior)
    (hLocalPrior : T.IsPrior localPrior)
    (hLikelihood : T.IsLikelihood likelihood) :
    T.IsPosterior (priorNBPosterior globalPrior localPrior likelihood) := by
  let cfg : RoleDisciplinedSelector T :=
    { globalPrior := globalPrior
      localPrior := localPrior
      likelihood := likelihood
      hGlobalPrior := hGlobalPrior
      hLocalPrior := hLocalPrior
      hLikelihood := hLikelihood }
  simpa [priorNBPosterior, posterior, pooledPrior] using
    (posterior_isPosterior (T := T) cfg)

theorem priorNBPosteriorTwoStage_isPosterior
    (T : OperatorRoleTheory Goal Fact)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (hGlobalPrior : T.IsPrior globalPrior)
    (hLocalPrior : T.IsPrior localPrior)
    (hLikelihood : T.IsLikelihood likelihood) :
    T.IsPosterior (priorNBPosteriorTwoStage globalPrior localPrior likelihood) := by
  have hpost :
      T.IsPosterior (priorNBPosterior globalPrior localPrior likelihood) :=
    priorNBPosterior_isPosterior
      (T := T) globalPrior localPrior likelihood hGlobalPrior hLocalPrior hLikelihood
  simpa [priorNBPosterior_eq_twoStage (globalPrior := globalPrior)
      (localPrior := localPrior) (likelihood := likelihood)] using hpost

theorem priorNB_ranking_commutation_normalization_iff
    (η : Fact -> ℝ)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal) (t : ℝ≥0∞) :
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((normalizeScorer t
            (priorNBPosterior globalPrior localPrior likelihood)).score g x)).toReal)
      ↔
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((normalizeScorer t
            (priorNBPosteriorTwoStage globalPrior localPrior likelihood)).score g x)).toReal) := by
  simpa [priorNBPosterior, priorNBPosteriorTwoStage] using
    (ranking_after_commutation_normalization_iff
      (η := η) (p₁ := globalPrior) (p₂ := localPrior)
      (likelihood := likelihood) (g := g) (t := t))

/-- Under the explicit task checklist, Prior-NB keeps the commutation law
and respects the finite top-k budget assumption. -/
theorem priorNB_assumptionChecklist_commutation_and_budget
    {Bin : Type*} [Fintype Fact]
    (A : PriorNBAssumptionChecklist Goal Fact Bin)
    (globalPrior localPrior likelihood : Scorer Goal Fact) :
    priorNBPosterior globalPrior localPrior likelihood =
      priorNBPosteriorTwoStage globalPrior localPrior likelihood
      ∧ A.topK ≤ Fintype.card Fact := by
  exact ⟨priorNBPosterior_eq_twoStage globalPrior localPrior likelihood, A.topK_le_pool⟩

/-- Under the explicit task checklist, ranking-transfer through
pool/update commutation + normalization is available as an iff statement. -/
theorem priorNB_assumptionChecklist_ranking_transfer
    {Bin : Type*} [Fintype Fact]
    (A : PriorNBAssumptionChecklist Goal Fact Bin)
    (η : Fact -> ℝ)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal) (t : ℝ≥0∞) :
    A.localExchangeabilityInBin →
      (BayesOptimalRanking η
        (fun x =>
          (Evidence.toStrength
            ((normalizeScorer t
              (priorNBPosterior globalPrior localPrior likelihood)).score g x)).toReal)
        ↔
      BayesOptimalRanking η
        (fun x =>
          (Evidence.toStrength
            ((normalizeScorer t
              (priorNBPosteriorTwoStage globalPrior localPrior likelihood)).score g x)).toReal)) := by
  intro _hLocalEx
  exact priorNB_ranking_commutation_normalization_iff η globalPrior localPrior likelihood g t

/-! ## PLN-named rule aliases (theorem-level, no new axioms)

These names mirror the selector architecture in PLN terms:
- contextual prior pooling via revision (`fuse` / `hplus`)
- posterior from prior-likelihood tensor update (`update`)
- normalized ranking transfer through commutation
-/

/-- `PLN.ContextualPriorRevision`:
global prior revised with local prior before likelihood update. -/
theorem PLN_ContextualPriorRevision
    (globalPrior localPrior likelihood : Scorer Goal Fact) :
    priorNBPosterior globalPrior localPrior likelihood =
      update (fuse globalPrior localPrior) likelihood := by
  rfl

/-- `PLN.NormalizedPriorLikelihoodTensor`:
pool-then-update and update-then-pool are equivalent under external-Bayesianity. -/
theorem PLN_NormalizedPriorLikelihoodTensor
    (globalPrior localPrior likelihood : Scorer Goal Fact) :
    priorNBPosterior globalPrior localPrior likelihood =
      priorNBPosteriorTwoStage globalPrior localPrior likelihood := by
  exact priorNBPosterior_eq_twoStage globalPrior localPrior likelihood

/-- `PLN.PriorNBRankingTransfer`:
normalized ranking transfer across the commuted Prior-NB forms. -/
theorem PLN_PriorNBRankingTransfer
    (η : Fact -> ℝ)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal) (t : ℝ≥0∞) :
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((normalizeScorer t
            (priorNBPosterior globalPrior localPrior likelihood)).score g x)).toReal)
      ↔
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((normalizeScorer t
            (priorNBPosteriorTwoStage globalPrior localPrior likelihood)).score g x)).toReal) := by
  exact priorNB_ranking_commutation_normalization_iff η globalPrior localPrior likelihood g t

end Mettapedia.Logic.PremiseSelection
