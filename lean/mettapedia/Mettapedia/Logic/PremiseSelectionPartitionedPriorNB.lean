import Mettapedia.Logic.PremiseSelectionPriorNB
import Mettapedia.Logic.PremiseSelectionLocalMixtureBridge

/-!
# Partitioned Normalized Prior-NB (Proof-Driven Composition)

This module composes the existing theorem stack into a partitioned Prior-NB layer:

- partitioned local priors are pooled via revision (`fuse`)
- pooled prior and likelihood are normalized
- posterior is built via tensor update (`update`)

It also records theorem-level ranking and TV-bound composition bridges used by the
proof-driven selector architecture.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical ENNReal BigOperators
open Mettapedia.Logic.PremiseSelectionOptimality
open Mettapedia.Logic.EvidenceQuantale

variable {Goal Fact Bin : Type*}
variable {TS : OperatorRoleTheoryScaled Goal Fact}
variable {TN : OperatorRoleTheoryNormalized Goal Fact}

/-! ## 1A. Partitioned prior closure -/

/-- Weighted partitioned prior is prior-typed under role closure assumptions.

`hZeroPrior` is required to anchor the empty partition. -/
theorem partitionedPrior_isPrior
    (bins : Finset Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞)
    (hZeroPrior : TS.IsPrior zeroScorer)
    (hLocal : ∀ b ∈ bins, TS.IsPrior (localPrior b)) :
    TS.IsPrior (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight) := by
  classical
  let P : Finset Bin → Prop :=
    fun bs =>
      (∀ b ∈ bs, TS.IsPrior (localPrior b)) →
        TS.IsPrior (partitionedPrior (Goal := Goal) (Fact := Fact) bs localPrior weight)
  have hP : ∀ bs, P bs := by
    intro bs
    refine Finset.induction_on bs ?hbase ?hstep
    · intro _h
      simpa [partitionedPrior_empty] using hZeroPrior
    · intro b s hbNotIn hs hmem
      have hbPrior : TS.IsPrior (localPrior b) := hmem b (by simp)
      have hsMem : ∀ b' ∈ s, TS.IsPrior (localPrior b') := by
        intro b' hb'
        exact hmem b' (by simp [hb'])
      have hsPrior :
          TS.IsPrior (partitionedPrior (Goal := Goal) (Fact := Fact) s localPrior weight) :=
        hs hsMem
      have hScaled : TS.IsPrior (scaleScorer (weight b) (localPrior b)) :=
        TS.prior_scale_closed (weight b) (localPrior b) hbPrior
      have hsplit :
          partitionedPrior (Goal := Goal) (Fact := Fact) (insert b s) localPrior weight
            =
          fuse
            (scaleScorer (weight b) (localPrior b))
            (partitionedPrior (Goal := Goal) (Fact := Fact) s localPrior weight) := by
        apply Scorer.ext
        intro g f
        simp [partitionedPrior, fuse, hbNotIn, Finset.sum_insert]
      rw [hsplit]
      exact TS.prior_fuse_closed _ _ hScaled hsPrior
  exact hP bins hLocal

/-! ## 1B. Partitioned normalized prior-likelihood composition -/

/-- Partitioned Prior-NB posterior: normalized pooled prior tensored with normalized likelihood. -/
noncomputable def partitionedPriorNBPosterior
    (bins : Finset Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞)
    (likelihood : Scorer Goal Fact)
    (tP tL : ℝ≥0∞) : Scorer Goal Fact :=
  update
    (normalizeScorer tP (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight))
    (normalizeScorer tL likelihood)

theorem partitionedPriorNBPosterior_isPosterior
    (bins : Finset Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞)
    (likelihood : Scorer Goal Fact)
    (tP tL : ℝ≥0∞)
    (hZeroPrior : TN.IsPrior zeroScorer)
    (hLocal : ∀ b ∈ bins, TN.IsPrior (localPrior b))
    (hLik : TN.IsLikelihood likelihood) :
    TN.IsPosterior (partitionedPriorNBPosterior
      (Goal := Goal) (Fact := Fact) bins localPrior weight likelihood tP tL) := by
  unfold partitionedPriorNBPosterior
  apply TN.posterior_from_update
  · -- Role-correct prior normalization is internalized in `OperatorRoleTheoryNormalized`.
    have hPrior :
        TN.IsPrior (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight) :=
      partitionedPrior_isPrior (TS := TN.toOperatorRoleTheoryScaled)
        bins localPrior weight hZeroPrior hLocal
    exact TN.prior_normalize_closed tP _ hPrior
  · exact TN.likelihood_normalize_closed tL _ hLik

/-- Strength lower-bound for normalized tensor composition (product floor). -/
theorem partitionedPriorNB_strength_ge_product
    (bins : Finset Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞)
    (likelihood : Scorer Goal Fact)
    (tP tL : ℝ≥0∞)
    (g : Goal) (f : Fact) :
    Evidence.toStrength
      ((partitionedPriorNBPosterior (Goal := Goal) (Fact := Fact)
          bins localPrior weight likelihood tP tL).score g f)
      ≥
    Evidence.toStrength
      ((normalizeScorer tP
          (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight)).score g f)
      *
    Evidence.toStrength ((normalizeScorer tL likelihood).score g f) := by
  unfold partitionedPriorNBPosterior update
  simpa using
    (Evidence.toStrength_tensor_ge
      ((normalizeScorer tP
          (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight)).score g f)
      ((normalizeScorer tL likelihood).score g f))

/-- Exact normalized tensor strength formula in nondegenerate denominator regime. -/
theorem partitionedPriorNB_strength_formula
    (bins : Finset Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞)
    (likelihood : Scorer Goal Fact)
    (tP tL : ℝ≥0∞)
    (g : Goal) (f : Fact)
    (hTot :
      (((normalizeScorer tP
          (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight)).score g f)
        * ((normalizeScorer tL likelihood).score g f)).total ≠ 0) :
    Evidence.toStrength
      ((partitionedPriorNBPosterior (Goal := Goal) (Fact := Fact)
          bins localPrior weight likelihood tP tL).score g f)
      =
    ((((normalizeScorer tP
          (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight)).score g f).pos)
      * (((normalizeScorer tL likelihood).score g f).pos))
      /
    (((((normalizeScorer tP
          (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight)).score g f).pos)
        * (((normalizeScorer tL likelihood).score g f).pos))
      +
      ((((normalizeScorer tP
          (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight)).score g f).neg)
        * (((normalizeScorer tL likelihood).score g f).neg))) := by
  unfold partitionedPriorNBPosterior update
  have hmain :
      Evidence.toStrength
        (((normalizeScorer tP
            (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight)).score g f)
          * ((normalizeScorer tL likelihood).score g f))
        =
      ((((normalizeScorer tP
            (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight)).score g f)
            * ((normalizeScorer tL likelihood).score g f)).pos)
        /
      ((((normalizeScorer tP
            (partitionedPrior (Goal := Goal) (Fact := Fact) bins localPrior weight)).score g f)
            * ((normalizeScorer tL likelihood).score g f)).total) := by
    simp [Evidence.toStrength, hTot]
  simpa [Evidence.tensor_def, Evidence.total] using hmain

/-! ## 1C. Ranking optimality transfer (partitioned composed score) -/

theorem partitionedPriorNB_ranking_optimal
    (bins : Finset Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞)
    (likelihood : Scorer Goal Fact)
    (tP tL : ℝ≥0∞)
    (η : Fact → ℝ)
    (g : Goal)
    (hPosterior :
      ∃ fPost : ℝ → ℝ, StrictMono fPost ∧
        (fun x =>
          (Evidence.toStrength
            ((partitionedPriorNBPosterior (Goal := Goal) (Fact := Fact)
              bins localPrior weight likelihood tP tL).score g x)).toReal)
          = fun x => fPost (η x)) :
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((partitionedPriorNBPosterior (Goal := Goal) (Fact := Fact)
            bins localPrior weight likelihood tP tL).score g x)).toReal) := by
  rcases hPosterior with ⟨fPost, hfPost, hsPost⟩
  exact ranking_optimal_of_strictMono η _ fPost hsPost hfPost

/-! ## 1D. TV-bound composition for partitioned local-mixture regime -/

theorem partitionedPrior_tv_bound
    (bins : Finset Bin)
    (tvErr : Bin → ℝ)
    (neighborhoodSize poolSize : Bin → ℕ)
    (hPerBin :
      ∀ b ∈ bins,
        tvErr b ≤
          ((neighborhoodSize b : ℝ) * ((neighborhoodSize b : ℝ) - 1)) /
          ((2 : ℝ) * (poolSize b : ℝ))) :
    (Finset.sum bins (fun b => tvErr b))
      ≤
    (Finset.sum bins (fun b =>
      ((neighborhoodSize b : ℝ) * ((neighborhoodSize b : ℝ) - 1)) /
      ((2 : ℝ) * (poolSize b : ℝ)))) := by
  exact Finset.sum_le_sum (fun b hb => hPerBin b hb)

/-! ## 1E. Single-bin sanity -/

/-- Single-bin partition pooling collapses to the scaled local expert. -/
theorem partitionedPrior_singleton
    (b : Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞) :
    partitionedPrior (Goal := Goal) (Fact := Fact) ({b} : Finset Bin) localPrior weight
      = scaleScorer (weight b) (localPrior b) := by
  apply Scorer.ext
  intro g f
  simp [partitionedPrior]

/-- Single-bin partitioned Prior-NB posterior is the normalized scaled-local prior
tensored with normalized likelihood. -/
theorem partitionedPriorNBPosterior_singleton
    (b : Bin)
    (localPrior : Bin → Scorer Goal Fact)
    (weight : Bin → ℝ≥0∞)
    (likelihood : Scorer Goal Fact)
    (tP tL : ℝ≥0∞) :
    partitionedPriorNBPosterior
      (Goal := Goal) (Fact := Fact)
      ({b} : Finset Bin) localPrior weight likelihood tP tL
      =
    update
      (normalizeScorer tP (scaleScorer (weight b) (localPrior b)))
      (normalizeScorer tL likelihood) := by
  simp [partitionedPriorNBPosterior, partitionedPrior_singleton]

end Mettapedia.Logic.PremiseSelection
