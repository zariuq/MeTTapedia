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

open scoped Classical ENNReal BigOperators

/-- Abstract checklist for operator-role correctness. -/
structure OperatorRoleTheory (Goal Fact : Type*) where
  IsPrior : Scorer Goal Fact → Prop
  IsLikelihood : Scorer Goal Fact → Prop
  IsPosterior : Scorer Goal Fact → Prop
  prior_fuse_closed :
    ∀ p₁ p₂, IsPrior p₁ → IsPrior p₂ → IsPrior (fuse p₁ p₂)
  posterior_from_update :
    ∀ p l, IsPrior p → IsLikelihood l → IsPosterior (update p l)

/-- Extension of operator-role theory with explicit closure under evidence scaling.

This captures the practical selector requirement that calibrated weighting/regraduation
of a prior (e.g. local-neighborhood gate mass) keeps it in the prior role. -/
structure OperatorRoleTheoryScaled (Goal Fact : Type*) extends OperatorRoleTheory Goal Fact where
  prior_scale_closed :
    ∀ w p, IsPrior p → IsPrior (scaleScorer w p)

/-- Extension of operator-role theory with normalization closure.

This internalizes the requirement that role-typed priors/likelihoods stay in-role
after evidence-total normalization (`normalizeScorer`). This is the exact closure
needed by normalized Prior-NB style selectors. -/
structure OperatorRoleTheoryNormalized (Goal Fact : Type*)
    extends OperatorRoleTheoryScaled Goal Fact where
  prior_normalize_closed :
    ∀ t p, IsPrior p → IsPrior (normalizeScorer t p)
  likelihood_normalize_closed :
    ∀ t l, IsLikelihood l → IsLikelihood (normalizeScorer t l)

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
variable {TS : OperatorRoleTheoryScaled Goal Fact}
variable {TN : OperatorRoleTheoryNormalized Goal Fact}

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

/-! ## Gated / scaled local-prior path -/

/-- Gated local-prior pooling: global prior revised with a scaled local prior. -/
noncomputable def gatedPooledPrior
    (cfg : RoleDisciplinedSelector TS.toOperatorRoleTheory) (wLocal : ℝ≥0∞) :
    Scorer Goal Fact :=
  fuse cfg.globalPrior (scaleScorer wLocal cfg.localPrior)

/-- Gated posterior: role-correct prior pooling then likelihood update. -/
noncomputable def gatedPosterior
    (cfg : RoleDisciplinedSelector TS.toOperatorRoleTheory) (wLocal : ℝ≥0∞) :
    Scorer Goal Fact :=
  update (gatedPooledPrior cfg wLocal) cfg.likelihood

theorem gatedPooledPrior_isPrior
    (cfg : RoleDisciplinedSelector TS.toOperatorRoleTheory) (wLocal : ℝ≥0∞) :
    TS.IsPrior (gatedPooledPrior cfg wLocal) := by
  unfold gatedPooledPrior
  exact TS.prior_fuse_closed _ _
    cfg.hGlobalPrior
    (TS.prior_scale_closed wLocal cfg.localPrior cfg.hLocalPrior)

theorem gatedPosterior_isPosterior
    (cfg : RoleDisciplinedSelector TS.toOperatorRoleTheory) (wLocal : ℝ≥0∞) :
    TS.IsPosterior (gatedPosterior cfg wLocal) := by
  unfold gatedPosterior
  exact TS.posterior_from_update _ _ (gatedPooledPrior_isPrior (TS := TS) cfg wLocal) cfg.hLikelihood

/-- Zero local gate cleanly falls back to the global-prior path. -/
theorem gatedPooledPrior_zero_local
    (cfg : RoleDisciplinedSelector TS.toOperatorRoleTheory) :
    gatedPooledPrior cfg 0 = cfg.globalPrior := by
  apply Scorer.ext
  intro g f
  simp [gatedPooledPrior, fuse, scaleScorer, scaleEvidence]
  have hz : ({ pos := 0, neg := 0 } : Mettapedia.Logic.EvidenceQuantale.Evidence) = 0 := rfl
  simp [hz] at *

theorem gatedPosterior_zero_local
    (cfg : RoleDisciplinedSelector TS.toOperatorRoleTheory) :
    gatedPosterior cfg 0 = update cfg.globalPrior cfg.likelihood := by
  simpa [gatedPosterior] using
    congrArg (fun p => update p cfg.likelihood) (gatedPooledPrior_zero_local (TS := TS) cfg)

/-! ## Partitioned weighted prior pooling -/

/-- Finite partition prior pooled by weighted revision (pointwise evidence sum). -/
noncomputable def partitionedPrior
    {Bin : Type*} (bins : Finset Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞) : Scorer Goal Fact :=
  ⟨fun g f => Finset.sum bins (fun b => (scaleScorer (weight b) (localPrior b)).score g f)⟩

@[simp] theorem partitionedPrior_empty
    {Bin : Type*}
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞) :
    partitionedPrior (Goal := Goal) (Fact := Fact) (bins := (∅ : Finset Bin)) localPrior weight
      = zeroScorer := by
  apply Scorer.ext
  intro g f
  change (0 : Mettapedia.Logic.EvidenceQuantale.Evidence) =
      (zeroScorer : Scorer Goal Fact).score g f
  change (0 : Mettapedia.Logic.EvidenceQuantale.Evidence) =
      ({ pos := 0, neg := 0 } : Mettapedia.Logic.EvidenceQuantale.Evidence)
  rfl

@[simp] theorem partitionedPrior_zero_weights
    {Bin : Type*}
    (bins : Finset Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞)
    (hzero : ∀ b ∈ bins, weight b = 0) :
    partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight = zeroScorer := by
  apply Scorer.ext
  intro g f
  simp [partitionedPrior, zeroScorer]
  refine Finset.sum_eq_zero ?_
  intro b hb
  have hb0 : weight b = 0 := hzero b hb
  simp [scaleEvidence, hb0]
  show ({ pos := 0, neg := 0 } : Mettapedia.Logic.EvidenceQuantale.Evidence) = 0
  rfl

/-- Permutation/order invariance for partitioned pooling (Finset extensionality). -/
theorem partitionedPrior_congr
    {Bin : Type*}
    {bins₁ bins₂ : Finset Bin}
    (hbins : bins₁ = bins₂)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞) :
    partitionedPrior (Goal := Goal) (Fact := Fact) bins₁ localPrior weight =
      partitionedPrior (Goal := Goal) (Fact := Fact) bins₂ localPrior weight := by
  simp [hbins]

end Mettapedia.Logic.PremiseSelection
