import Mettapedia.Logic.PremiseSelectionPartitionedPriorNB
import Mettapedia.Logic.PremiseSelectionSelectorSpec

/-!
# Best-PLN Premise Selector (Draft, Proof-Driven)

This module gives a concrete draft of the currently best-supported PLN selector
shape from the formal stack:

1. Build a **partitioned local prior** via revision (`hplus` / `fuse`)
2. Fuse with a **global prior**
3. Normalize prior and likelihood totals in a finite nonzero regime
4. Compose sequentially with tensor (`update`)

So the draft posterior is:

`update (normalizeScorer tP (fuse globalPrior localPrior))
        (normalizeScorer tL likelihood)`

This matches the operator-role discipline and preserves the
local-mixture + normalization semantics proved elsewhere.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical ENNReal BigOperators
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PremiseSelectionOptimality

variable {Goal Fact Bin : Type*}
variable {TN : OperatorRoleTheoryNormalized Goal Fact}

/-- Draft parameter bundle for the proof-driven Best-PLN selector. -/
structure BestPLNConfig (Goal Fact Bin : Type*) where
  bins : Finset Bin
  weight : Bin → ℝ≥0∞
  tPrior : ℝ≥0∞
  tLik : ℝ≥0∞
  tPrior_ne_zero : tPrior ≠ 0
  tLik_ne_zero : tLik ≠ 0
  tPrior_ne_top : tPrior ≠ ⊤
  tLik_ne_top : tLik ≠ ⊤

/-- Partitioned local prior used by the Best-PLN draft. -/
noncomputable def bestLocalPrior
    (cfg : BestPLNConfig Goal Fact Bin)
    (localPriorByBin : Bin → Scorer Goal Fact) : Scorer Goal Fact :=
  partitionedPrior (Goal := Goal) (Fact := Fact) cfg.bins localPriorByBin cfg.weight

/-- Fused prior (global + partitioned local) used by the Best-PLN draft. -/
noncomputable def bestPooledPrior
    (cfg : BestPLNConfig Goal Fact Bin)
    (globalPrior : Scorer Goal Fact)
    (localPriorByBin : Bin → Scorer Goal Fact) : Scorer Goal Fact :=
  fuse globalPrior (bestLocalPrior (Goal := Goal) (Fact := Fact) cfg localPriorByBin)

/-- Best-PLN draft posterior:
normalize fused prior and likelihood, then compose by tensor update. -/
noncomputable def bestPosterior
    (cfg : BestPLNConfig Goal Fact Bin)
    (globalPrior : Scorer Goal Fact)
    (localPriorByBin : Bin → Scorer Goal Fact)
    (likelihood : Scorer Goal Fact) : Scorer Goal Fact :=
  update
    (normalizeScorer cfg.tPrior
      (bestPooledPrior (Goal := Goal) (Fact := Fact) cfg globalPrior localPriorByBin))
    (normalizeScorer cfg.tLik likelihood)

/-- Local prior is prior-typed under scaled role closure. -/
theorem bestLocalPrior_isPrior
    (cfg : BestPLNConfig Goal Fact Bin)
    (localPriorByBin : Bin → Scorer Goal Fact)
    (hZeroPrior : TN.IsPrior zeroScorer)
    (hLocal : ∀ b ∈ cfg.bins, TN.IsPrior (localPriorByBin b)) :
    TN.IsPrior (bestLocalPrior (Goal := Goal) (Fact := Fact) cfg localPriorByBin) := by
  simpa [bestLocalPrior] using
    (partitionedPrior_isPrior (TS := TN.toOperatorRoleTheoryScaled)
      (bins := cfg.bins)
      (localPrior := localPriorByBin)
      (weight := cfg.weight)
      hZeroPrior hLocal)

/-- Fused prior (global + local) is prior-typed. -/
theorem bestPooledPrior_isPrior
    (cfg : BestPLNConfig Goal Fact Bin)
    (globalPrior : Scorer Goal Fact)
    (localPriorByBin : Bin → Scorer Goal Fact)
    (hGlobalPrior : TN.IsPrior globalPrior)
    (hZeroPrior : TN.IsPrior zeroScorer)
    (hLocal : ∀ b ∈ cfg.bins, TN.IsPrior (localPriorByBin b)) :
    TN.IsPrior (bestPooledPrior (Goal := Goal) (Fact := Fact) cfg globalPrior localPriorByBin) := by
  unfold bestPooledPrior
  exact TN.prior_fuse_closed _ _ hGlobalPrior
    (bestLocalPrior_isPrior (TN := TN) (cfg := cfg) localPriorByBin hZeroPrior hLocal)

/-- Role-correctness theorem for the Best-PLN draft posterior. -/
theorem bestPosterior_isPosterior
    (cfg : BestPLNConfig Goal Fact Bin)
    (globalPrior : Scorer Goal Fact)
    (localPriorByBin : Bin → Scorer Goal Fact)
    (likelihood : Scorer Goal Fact)
    (hGlobalPrior : TN.IsPrior globalPrior)
    (hZeroPrior : TN.IsPrior zeroScorer)
    (hLocal : ∀ b ∈ cfg.bins, TN.IsPrior (localPriorByBin b))
    (hLik : TN.IsLikelihood likelihood) :
    TN.IsPosterior (bestPosterior
      (Goal := Goal) (Fact := Fact) cfg globalPrior localPriorByBin likelihood) := by
  unfold bestPosterior
  apply TN.posterior_from_update
  · exact TN.prior_normalize_closed _ _
      (bestPooledPrior_isPrior (TN := TN) (cfg := cfg)
        (globalPrior := globalPrior) (localPriorByBin := localPriorByBin)
        hGlobalPrior hZeroPrior hLocal)
  · exact TN.likelihood_normalize_closed _ _ hLik

/-- Strength formula for normalized fusion weights (prior vs likelihood totals). -/
theorem bestPosterior_strength_linear_pooling
    (cfg : BestPLNConfig Goal Fact Bin)
    (globalPrior : Scorer Goal Fact)
    (localPriorByBin : Bin → Scorer Goal Fact)
    (likelihood : Scorer Goal Fact)
    (g : Goal) (f : Fact) :
    Evidence.toStrength
      ((fuse
          (normalizeScorer cfg.tPrior
            (bestPooledPrior (Goal := Goal) (Fact := Fact) cfg globalPrior localPriorByBin))
          (normalizeScorer cfg.tLik likelihood)).score g f)
      =
      (cfg.tPrior / (cfg.tPrior + cfg.tLik))
          * Evidence.toStrength
              ((normalizeScorer cfg.tPrior
                (bestPooledPrior (Goal := Goal) (Fact := Fact) cfg globalPrior localPriorByBin)).score g f)
      + (cfg.tLik / (cfg.tPrior + cfg.tLik))
          * Evidence.toStrength ((normalizeScorer cfg.tLik likelihood).score g f) := by
  exact
    fuse_toStrength_normalized_totals
      (s₁ := bestPooledPrior (Goal := Goal) (Fact := Fact) cfg globalPrior localPriorByBin)
      (s₂ := likelihood)
      (g := g) (f := f)
      (t₁ := cfg.tPrior) (t₂ := cfg.tLik)
      cfg.tPrior_ne_zero cfg.tLik_ne_zero
      (by
        intro hsum
        have h0 : cfg.tPrior = 0 := (add_eq_zero.mp hsum).1
        exact cfg.tPrior_ne_zero h0)
      cfg.tPrior_ne_top cfg.tLik_ne_top

/-- Ranking-ready wrapper: if the Best-PLN score is a strict monotone transform
of a Bayes relevance target, ranking is Bayes-optimal. -/
theorem bestPosterior_ranking_optimal
    (cfg : BestPLNConfig Goal Fact Bin)
    (globalPrior : Scorer Goal Fact)
    (localPriorByBin : Bin → Scorer Goal Fact)
    (likelihood : Scorer Goal Fact)
    (η : Fact → ℝ) (g : Goal)
    (hPosterior :
      ∃ fPost : ℝ → ℝ, StrictMono fPost ∧
        (fun x =>
          (Evidence.toStrength
            ((bestPosterior (Goal := Goal) (Fact := Fact)
              cfg globalPrior localPriorByBin likelihood).score g x)).toReal)
          = fun x => fPost (η x)) :
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((bestPosterior (Goal := Goal) (Fact := Fact)
            cfg globalPrior localPriorByBin likelihood).score g x)).toReal) := by
  rcases hPosterior with ⟨fPost, hfPost, hsPost⟩
  exact ranking_optimal_of_strictMono η _ fPost hsPost hfPost

/-- Zero local-bin mass fallback:
if all partition weights are zero, Best-PLN reduces to the global-prior path. -/
theorem bestPosterior_zeroLocalMass_fallback
    (cfg : BestPLNConfig Goal Fact Bin)
    (globalPrior : Scorer Goal Fact)
    (localPriorByBin : Bin → Scorer Goal Fact)
    (likelihood : Scorer Goal Fact)
    (hzero : ∀ b ∈ cfg.bins, cfg.weight b = 0) :
    bestPosterior (Goal := Goal) (Fact := Fact) cfg globalPrior localPriorByBin likelihood
      =
    update (normalizeScorer cfg.tPrior globalPrior) (normalizeScorer cfg.tLik likelihood) := by
  have hLocalZero :
      bestLocalPrior (Goal := Goal) (Fact := Fact) cfg localPriorByBin = zeroScorer := by
    unfold bestLocalPrior
    simpa using
      (partitionedPrior_zero_weights (Goal := Goal) (Fact := Fact)
        (bins := cfg.bins) (localPrior := localPriorByBin) (weight := cfg.weight) hzero)
  have hPooled :
      bestPooledPrior (Goal := Goal) (Fact := Fact) cfg globalPrior localPriorByBin = globalPrior := by
    apply Scorer.ext
    intro g f
    simp [bestPooledPrior, hLocalZero, fuse]
  simp [bestPosterior, hPooled]

/-- Bridge theorem mention: k-NN positive-evidence bridge is available for local prior design. -/
theorem bestPLN_knnBridge_available {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) (phi : Fact) :
    (plnKnnEvidence goal N near deps tau2 phi).pos =
      knnRelevanceENN goal N near deps tau2 phi := by
  exact PLN_hplusPos_eq_knnRelevance goal N near deps tau2 phi

/-- Bridge theorem mention: revision-strength linear pooling law is available. -/
theorem bestPLN_revisionLinearPool_available
    (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact)
    (h₁ : (s₁.score g f).total ≠ 0)
    (h₂ : (s₂.score g f).total ≠ 0)
    (h₁₂ : ((s₁.score g f + s₂.score g f).total) ≠ 0)
    (h₁_top : (s₁.score g f).total ≠ ⊤)
    (h₂_top : (s₂.score g f).total ≠ ⊤) :
    Evidence.toStrength ((fuse s₁ s₂).score g f) =
      ((s₁.score g f).total / (s₁.score g f + s₂.score g f).total) * Evidence.toStrength (s₁.score g f)
      + ((s₂.score g f).total / (s₁.score g f + s₂.score g f).total) * Evidence.toStrength (s₂.score g f) := by
  exact PLN_revisionStrength_eq_linearPool s₁ s₂ g f h₁ h₂ h₁₂ h₁_top h₂_top

end Mettapedia.Logic.PremiseSelection
