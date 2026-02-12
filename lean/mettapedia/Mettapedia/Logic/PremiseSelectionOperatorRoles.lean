import Mettapedia.Logic.PremiseSelectionExternalBayesianity

/-!
# Operator-Role Discipline for Premise Selection

This module encodes an explicit theorem-level checklist for role-correct composition:

- priors are pooled via `fuse` (revision / `hplus`)
- likelihood is applied via `update` (tensor)
- posterior is the result of `update (fuse priorGlobal priorLocal) likelihood`

It also proves equivalence with the two-stage form
`fuse (update priorGlobal likelihood) (update priorLocal likelihood)` via
external-Bayesianity commutation.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical ENNReal

/-- Abstract checklist for operator-role correctness. -/
structure OperatorRoleTheory (Goal Fact : Type*) where
  IsPrior : Scorer Goal Fact → Prop
  IsLikelihood : Scorer Goal Fact → Prop
  IsPosterior : Scorer Goal Fact → Prop
  prior_fuse_closed :
    ∀ p₁ p₂, IsPrior p₁ → IsPrior p₂ → IsPrior (fuse p₁ p₂)
  posterior_from_update :
    ∀ p l, IsPrior p → IsLikelihood l → IsPosterior (update p l)

/-- A premise selector decomposed into role-typed components. -/
structure RoleDisciplinedSelector {Goal Fact : Type*} (T : OperatorRoleTheory Goal Fact) where
  globalPrior : Scorer Goal Fact
  localPrior : Scorer Goal Fact
  likelihood : Scorer Goal Fact
  hGlobalPrior : T.IsPrior globalPrior
  hLocalPrior : T.IsPrior localPrior
  hLikelihood : T.IsLikelihood likelihood

variable {Goal Fact : Type*}
variable {T : OperatorRoleTheory Goal Fact}

/-- Canonical prior pooling step (revision). -/
noncomputable def pooledPrior (cfg : RoleDisciplinedSelector T) : Scorer Goal Fact :=
  fuse cfg.globalPrior cfg.localPrior

/-- Canonical posterior step: pooled prior then likelihood update (tensor). -/
noncomputable def posterior (cfg : RoleDisciplinedSelector T) : Scorer Goal Fact :=
  update (pooledPrior cfg) cfg.likelihood

/-- Equivalent two-stage form: update each prior then pool. -/
noncomputable def posteriorTwoStage (cfg : RoleDisciplinedSelector T) : Scorer Goal Fact :=
  fuse (update cfg.globalPrior cfg.likelihood) (update cfg.localPrior cfg.likelihood)

theorem pooledPrior_isPrior (cfg : RoleDisciplinedSelector T) :
    T.IsPrior (pooledPrior cfg) := by
  exact T.prior_fuse_closed _ _ cfg.hGlobalPrior cfg.hLocalPrior

theorem posterior_isPosterior (cfg : RoleDisciplinedSelector T) :
    T.IsPosterior (posterior cfg) := by
  exact T.posterior_from_update _ _ (pooledPrior_isPrior (T := T) cfg) cfg.hLikelihood

/-- Role-correct pooled-then-update equals update-then-pool (external-Bayesian form). -/
theorem posterior_eq_twoStage (cfg : RoleDisciplinedSelector T) :
    posterior cfg = posteriorTwoStage cfg := by
  unfold posterior posteriorTwoStage pooledPrior
  simpa using
    (externalBayesianity_hplus_tensor
      (s₁ := cfg.globalPrior) (s₂ := cfg.localPrior) (likelihood := cfg.likelihood)).symm

theorem posteriorTwoStage_isPosterior (cfg : RoleDisciplinedSelector T) :
    T.IsPosterior (posteriorTwoStage cfg) := by
  simpa [posterior_eq_twoStage (T := T) cfg] using posterior_isPosterior (T := T) cfg

end Mettapedia.Logic.PremiseSelection
