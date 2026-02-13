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
open Mettapedia.Logic.EvidenceQuantale

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

/-- Practical finite-normalized variant:
normalization closure is required only in the finite nonzero regime (`t ≠ 0`, `t ≠ ⊤`). -/
structure OperatorRoleTheoryFiniteNormalized (Goal Fact : Type*)
    extends OperatorRoleTheory Goal Fact where
  prior_normalize_closed_finite :
    ∀ t p, t ≠ 0 → t ≠ ⊤ → IsPrior p → IsPrior (normalizeScorer t p)
  likelihood_normalize_closed_finite :
    ∀ t l, t ≠ 0 → t ≠ ⊤ → IsLikelihood l → IsLikelihood (normalizeScorer t l)

/-- Evidence totals are finite (not `⊤`) at every goal/fact point. -/
def IsFiniteScorer {Goal Fact : Type*} (s : Scorer Goal Fact) : Prop :=
  ∀ g f, (s.score g f).total ≠ ⊤

/-- Evidence totals are finite and nonzero at every goal/fact point. -/
def IsFiniteNonzeroScorer {Goal Fact : Type*} (s : Scorer Goal Fact) : Prop :=
  ∀ g f, (s.score g f).total ≠ 0 ∧ (s.score g f).total ≠ ⊤

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

/-! ## Concrete non-vacuous normalized role model

This model is intentionally explicit and non-vacuous:
- Priors/likelihoods/posteriors are scorers whose evidence is **negative-only**
  (positive coordinate `= 0`) at every goal/fact point.
- It is closed under `fuse`, `update`, `scaleScorer`, and `normalizeScorer`.

This gives a fully concrete `OperatorRoleTheoryNormalized` instance showing that
the class is realizable with semantics-first constraints (not `True` placeholders).
-/

/-- Negative-only semantic role predicate: every score has zero positive evidence. -/
def IsNegOnlyScorer {Goal Fact : Type*} (s : Scorer Goal Fact) : Prop :=
  ∀ g f, (s.score g f).pos = 0

lemma toStrength_eq_zero_of_pos_zero (e : Evidence) (hpos : e.pos = 0) :
    Evidence.toStrength e = 0 := by
  unfold Evidence.toStrength
  by_cases htot : e.total = 0
  · simp [htot]
  · simp [htot, hpos]

/-- A concrete, non-vacuous normalized role theory built from negative-only evidence. -/
noncomputable def negOnlyOperatorRoleTheoryNormalized (Goal Fact : Type*) :
    OperatorRoleTheoryNormalized Goal Fact where
  IsPrior := IsNegOnlyScorer
  IsLikelihood := IsNegOnlyScorer
  IsPosterior := IsNegOnlyScorer
  prior_fuse_closed := by
    intro p₁ p₂ hp₁ hp₂ g f
    simp [fuse, Evidence.hplus_def, hp₁ g f, hp₂ g f]
  posterior_from_update := by
    intro p l hp hl g f
    simp [update, Evidence.tensor_def, hp g f, hl g f]
  prior_scale_closed := by
    intro w p hp g f
    simp [scaleScorer, scaleEvidence, hp g f]
  prior_normalize_closed := by
    intro t p hp g f
    have hs : Evidence.toStrength (p.score g f) = 0 :=
      toStrength_eq_zero_of_pos_zero (e := p.score g f) (hp g f)
    simp [normalizeScorer, normalizeEvidence, hs]
  likelihood_normalize_closed := by
    intro t l hl g f
    have hs : Evidence.toStrength (l.score g f) = 0 :=
      toStrength_eq_zero_of_pos_zero (e := l.score g f) (hl g f)
    simp [normalizeScorer, normalizeEvidence, hs]

/-- The concrete role model is non-vacuous: some scorers satisfy it. -/
theorem negOnlyOperatorRoleTheoryNormalized_exists_prior
    (Goal Fact : Type*) :
    ∃ p : Scorer Goal Fact,
      (negOnlyOperatorRoleTheoryNormalized Goal Fact).IsPrior p := by
  refine ⟨zeroScorer, ?_⟩
  intro g f
  simp [zeroScorer, Evidence.zero]

/-- The concrete role model is non-vacuous: not every scorer is a prior. -/
theorem negOnlyOperatorRoleTheoryNormalized_not_all_priors
    (Goal Fact : Type*) [Nonempty Goal] [Nonempty Fact] :
    ∃ s : Scorer Goal Fact,
      ¬ (negOnlyOperatorRoleTheoryNormalized Goal Fact).IsPrior s := by
  let g0 : Goal := Classical.choice ‹Nonempty Goal›
  let f0 : Fact := Classical.choice ‹Nonempty Fact›
  refine ⟨constScorer (Goal := Goal) (Fact := Fact) 1, ?_⟩
  intro hs
  have h0 : ((constScorer (Goal := Goal) (Fact := Fact) 1).score g0 f0).pos = 0 := hs g0 f0
  have h1 : ((constScorer (Goal := Goal) (Fact := Fact) 1).score g0 f0).pos = (1 : ℝ≥0∞) := by
    rfl
  have : (1 : ℝ≥0∞) = 0 := by
    calc
      (1 : ℝ≥0∞) = ((constScorer (Goal := Goal) (Fact := Fact) 1).score g0 f0).pos := by
        simpa using h1.symm
      _ = 0 := h0
  exact one_ne_zero this

/-! ## Concrete finite nonzero normalized regime

This second role model tracks the practically relevant regime where normalized totals
are finite and nonzero (`t ≠ 0`, `t ≠ ⊤`). Unlike `OperatorRoleTheoryNormalized`,
its normalization closure is intentionally scoped to this regime.
-/

/-- A concrete finite-nonzero normalized role model. -/
noncomputable def finiteNonzeroOperatorRoleTheoryFiniteNormalized (Goal Fact : Type*) :
    OperatorRoleTheoryFiniteNormalized Goal Fact where
  IsPrior := IsFiniteNonzeroScorer
  IsLikelihood := IsFiniteNonzeroScorer
  IsPosterior := IsFiniteScorer
  prior_fuse_closed := by
    intro p₁ p₂ hp₁ hp₂ g f
    rcases hp₁ g f with ⟨h₁0, h₁top⟩
    rcases hp₂ g f with ⟨h₂0, h₂top⟩
    refine ⟨?_, ?_⟩
    · intro hsum
      have hsum' : (p₁.score g f).total + (p₂.score g f).total = 0 := by
        simpa [fuse_total] using hsum
      exact h₁0 (add_eq_zero.mp hsum').1
    · have hsum_top : (p₁.score g f).total + (p₂.score g f).total ≠ ⊤ := by
        exact WithTop.add_ne_top.mpr ⟨h₁top, h₂top⟩
      simpa [fuse_total] using hsum_top
  posterior_from_update := by
    intro p l hp hl g f
    rcases hp g f with ⟨_, hpTop⟩
    rcases hl g f with ⟨_, hlTop⟩
    have hpTot_lt : (p.score g f).total < ⊤ := lt_top_iff_ne_top.mpr hpTop
    have hlTot_lt : (l.score g f).total < ⊤ := lt_top_iff_ne_top.mpr hlTop
    have hpPos_le : (p.score g f).pos ≤ (p.score g f).total := by
      simp [Evidence.total]
    have hpNeg_le : (p.score g f).neg ≤ (p.score g f).total := by
      simp [Evidence.total]
    have hlPos_le : (l.score g f).pos ≤ (l.score g f).total := by
      simp [Evidence.total]
    have hlNeg_le : (l.score g f).neg ≤ (l.score g f).total := by
      simp [Evidence.total]
    have hpPos_top : (p.score g f).pos ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hpPos_le hpTot_lt)
    have hpNeg_top : (p.score g f).neg ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hpNeg_le hpTot_lt)
    have hlPos_top : (l.score g f).pos ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hlPos_le hlTot_lt)
    have hlNeg_top : (l.score g f).neg ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hlNeg_le hlTot_lt)
    have hmulPos_top :
        (p.score g f).pos * (l.score g f).pos ≠ ⊤ := ENNReal.mul_ne_top hpPos_top hlPos_top
    have hmulNeg_top :
        (p.score g f).neg * (l.score g f).neg ≠ ⊤ := ENNReal.mul_ne_top hpNeg_top hlNeg_top
    have hsum_top :
        (p.score g f).pos * (l.score g f).pos + (p.score g f).neg * (l.score g f).neg ≠ ⊤ := by
      exact WithTop.add_ne_top.mpr ⟨hmulPos_top, hmulNeg_top⟩
    simpa [update, Evidence.tensor_def, Evidence.total] using hsum_top
  prior_normalize_closed_finite := by
    intro t p ht0 htTop _hp g f
    refine ⟨?_, ?_⟩
    · simpa [normalizeScorer_total] using ht0
    · simpa [normalizeScorer_total] using htTop
  likelihood_normalize_closed_finite := by
    intro t l ht0 htTop _hl g f
    refine ⟨?_, ?_⟩
    · simpa [normalizeScorer_total] using ht0
    · simpa [normalizeScorer_total] using htTop

/-- The finite nonzero regime is non-vacuous: normalized constants inhabit it. -/
theorem finiteNonzeroOperatorRoleTheoryFiniteNormalized_exists_prior
    (Goal Fact : Type*) :
    ∃ p : Scorer Goal Fact,
      (finiteNonzeroOperatorRoleTheoryFiniteNormalized Goal Fact).IsPrior p := by
  refine ⟨normalizeScorer (t := (1 : ℝ≥0∞)) (s := (zeroScorer : Scorer Goal Fact)), ?_⟩
  intro g f
  constructor
  · have h1 : (1 : ℝ≥0∞) ≠ 0 := by simp
    simp [normalizeScorer_total, h1]
  · have h1top : (1 : ℝ≥0∞) ≠ ⊤ := by simp
    simp [normalizeScorer_total, h1top]

/-- The finite nonzero regime is non-vacuous: zero scorer is excluded. -/
theorem finiteNonzeroOperatorRoleTheoryFiniteNormalized_not_all_priors
    (Goal Fact : Type*) [Nonempty Goal] [Nonempty Fact] :
    ∃ s : Scorer Goal Fact,
      ¬ (finiteNonzeroOperatorRoleTheoryFiniteNormalized Goal Fact).IsPrior s := by
  let g0 : Goal := Classical.choice ‹Nonempty Goal›
  let f0 : Fact := Classical.choice ‹Nonempty Fact›
  refine ⟨zeroScorer, ?_⟩
  intro hs
  have h0 : ((zeroScorer : Scorer Goal Fact).score g0 f0).total ≠ 0 := (hs g0 f0).1
  exact h0 (by simp [zeroScorer, Evidence.zero, Evidence.total])

/-- Practical closure lemma: normalization by finite nonzero total yields a prior in this model. -/
theorem finiteNonzeroOperatorRoleTheoryFiniteNormalized_prior_from_normalize
    (Goal Fact : Type*) (t : ℝ≥0∞) (ht0 : t ≠ 0) (htTop : t ≠ ⊤) (p : Scorer Goal Fact) :
    (finiteNonzeroOperatorRoleTheoryFiniteNormalized Goal Fact).IsPrior
      (normalizeScorer t p) := by
  intro g f
  constructor
  · simpa [normalizeScorer_total] using ht0
  · simpa [normalizeScorer_total] using htTop

end Mettapedia.Logic.PremiseSelection
