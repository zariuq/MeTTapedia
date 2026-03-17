import Mettapedia.Logic.PremiseSelectionSelectorSpec
import Mettapedia.Logic.PremiseSelectionRankingStability
import Mettapedia.Logic.PremiseSelectionCoverage

/-!
# Chapter 13 Inference-Control Core (Composed Theorems)

This module provides theorem-level Chapter-13 composition endpoints that internalize
the "inference control" spine:

1. selector defaults + checklist obligations
2. Prior-NB commutation ranking transfer
3. perturbation/margin ranking stability
4. greedy coverage lower bounds

The goal is to expose these as reusable core guarantees, not only as tests/canaries.
-/

namespace Mettapedia.Logic.PLNInferenceControlCore

open Mettapedia.Logic.PremiseSelection
open Mettapedia.Logic.PremiseSelectionOptimality
open Mettapedia.Logic.EvidenceQuantale

/-! ## Canonical Chapter-13 score channels under selector defaults -/

/-- Chapter-13 pooled score channel:
normalize the pooled Prior-NB posterior at selector default prior-total and project strength. -/
noncomputable def ch13ScorePooled
    {Goal Fact : Type*} [Fintype Fact]
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal) : Fact → ℝ :=
  fun x =>
    (BinaryEvidence.toStrength
      ((normalizeScorer (selectorDefaults_halfGate Goal Fact).tPrior
        (priorNBPosterior globalPrior localPrior likelihood)).score g x)).toReal

/-- Chapter-13 two-stage score channel:
normalize the commuted Prior-NB posterior at selector default prior-total and project strength. -/
noncomputable def ch13ScoreTwoStage
    {Goal Fact : Type*} [Fintype Fact]
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal) : Fact → ℝ :=
  fun x =>
    (BinaryEvidence.toStrength
      ((normalizeScorer (selectorDefaults_halfGate Goal Fact).tPrior
        (priorNBPosteriorTwoStage globalPrior localPrior likelihood)).score g x)).toReal

/-- Core Chapter-13 selector theorem:
defaults discharge budget + gate-range obligations and expose pooled/two-stage ranking equivalence. -/
theorem ch13_selector_default_ranking_iff
    {Goal Fact Bin : Type*} [Fintype Fact]
    (A : PriorNBAssumptionChecklist Goal Fact Bin)
    (η : Fact → ℝ)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal)
    (hLocal : A.localExchangeabilityInBin) :
    A.topK ≤ Fintype.card Fact
      ∧ (∀ g' f',
          0 ≤ (selectorDefaults_halfGate Goal Fact).gate g' f'
            ∧ (selectorDefaults_halfGate Goal Fact).gate g' f' ≤ 1)
      ∧ (BayesOptimalRanking η (ch13ScorePooled globalPrior localPrior likelihood g)
          ↔
          BayesOptimalRanking η (ch13ScoreTwoStage globalPrior localPrior likelihood g)) := by
  simpa [ch13ScorePooled, ch13ScoreTwoStage] using
    (selectorSpec_default_priorNB_ranking_transfer
      (A := A) (η := η)
      (globalPrior := globalPrior) (localPrior := localPrior)
      (likelihood := likelihood) (g := g) hLocal)

/-- If two-stage Prior-NB ranking is Bayes-optimal, then pooled Prior-NB ranking remains
Bayes-optimal under bounded perturbations and strict pairwise margins. -/
theorem ch13_stable_pooled_of_twoStage
    {Goal Fact Bin : Type*} [Fintype Fact]
    (A : PriorNBAssumptionChecklist Goal Fact Bin)
    (η : Fact → ℝ)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal)
    (hLocal : A.localExchangeabilityInBin)
    (δ : Fact → ℝ) (ε : ℝ)
    (hTwoStage :
      BayesOptimalRanking η (ch13ScoreTwoStage globalPrior localPrior likelihood g))
    (hbound : ∀ x, |δ x| ≤ ε)
    (hmargin : ∀ x y, η x < η y →
      ch13ScorePooled globalPrior localPrior likelihood g y
        - ch13ScorePooled globalPrior localPrior likelihood g x > 2 * ε)
    (htie : ∀ x y, η x = η y → δ x = δ y) :
    BayesOptimalRanking η
      (perturbedScore (ch13ScorePooled globalPrior localPrior likelihood g) δ) := by
  have hSel :=
    ch13_selector_default_ranking_iff
      (A := A) (η := η)
      (globalPrior := globalPrior) (localPrior := localPrior)
      (likelihood := likelihood) (g := g) hLocal
  have hPooled :
      BayesOptimalRanking η (ch13ScorePooled globalPrior localPrior likelihood g) :=
    hSel.2.2.mpr hTwoStage
  exact bayesRanking_stable_of_margin_and_tie_equivariant
    (η := η) (s := ch13ScorePooled globalPrior localPrior likelihood g)
    (δ := δ) (ε := ε)
    hPooled hbound hmargin htie

/-- Chapter-13 one-call composed core theorem:
selector defaults + ranking transfer + perturbation stability + greedy-coverage bound. -/
theorem ch13_inferenceControl_end_to_end
    {Goal Fact Bin : Type*} [Fintype Fact] [DecidableEq Fact]
    (A : PriorNBAssumptionChecklist Goal Fact Bin)
    (η : Fact → ℝ)
    (globalPrior localPrior likelihood : Scorer Goal Fact)
    (g : Goal)
    (hLocal : A.localExchangeabilityInBin)
    (δ : Fact → ℝ) (ε : ℝ)
    (hTwoStage :
      BayesOptimalRanking η (ch13ScoreTwoStage globalPrior localPrior likelihood g))
    (hbound : ∀ x, |δ x| ≤ ε)
    (hmargin : ∀ x y, η x < η y →
      ch13ScorePooled globalPrior localPrior likelihood g y
        - ch13ScorePooled globalPrior localPrior likelihood g x > 2 * ε)
    (htie : ∀ x y, η x = η y → δ x = δ y)
    (D G : Finset Fact)
    (hGreedy : GreedyChain D A.topK G) :
    A.topK ≤ Fintype.card Fact
      ∧ (∀ g' f',
          0 ≤ (selectorDefaults_halfGate Goal Fact).gate g' f'
            ∧ (selectorDefaults_halfGate Goal Fact).gate g' f' ≤ 1)
      ∧ BayesOptimalRanking η
          (perturbedScore (ch13ScorePooled globalPrior localPrior likelihood g) δ)
      ∧ (1 - Real.exp (-1)) * (Nat.min A.topK D.card : ℝ) ≤ dependencyCoverage D G := by
  have hSel :=
    ch13_selector_default_ranking_iff
      (A := A) (η := η)
      (globalPrior := globalPrior) (localPrior := localPrior)
      (likelihood := likelihood) (g := g) hLocal
  refine ⟨hSel.1, hSel.2.1, ?_, ?_⟩
  · exact ch13_stable_pooled_of_twoStage
      (A := A) (η := η)
      (globalPrior := globalPrior) (localPrior := localPrior)
      (likelihood := likelihood) (g := g)
      hLocal δ ε hTwoStage hbound hmargin htie
  · exact greedyChain_one_minus_exp_bound_sharp
      (D := D) (G := G) (k := A.topK) hGreedy A.topK_pos

end Mettapedia.Logic.PLNInferenceControlCore
