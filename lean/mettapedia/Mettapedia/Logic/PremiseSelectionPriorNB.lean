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

end Mettapedia.Logic.PremiseSelection
