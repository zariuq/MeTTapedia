import Mettapedia.Logic.PLNInferenceControlAlgorithms

/-!
# Chapter 13 Worked Examples

Concrete finite fixtures that instantiate the Chapter-13 inference-control pipeline
with explicit scorers, checklist assumptions, and a dependency set.
-/

namespace Mettapedia.Logic.PLNInferenceControlExamples

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PremiseSelection
open Mettapedia.Logic.PremiseSelectionOptimality
open Mettapedia.Logic.PLNInferenceControlCore
open Mettapedia.Logic.PLNInferenceControlAlgorithms

noncomputable section

/-- Finite fixture scorer emphasizing `true` over `false`. -/
def ch13_globalPriorBool : Scorer Bool Bool :=
  ⟨fun _ f => if f then ⟨4, 1⟩ else ⟨1, 4⟩⟩

/-- Finite fixture local scorer with weaker but aligned bias. -/
def ch13_localPriorBool : Scorer Bool Bool :=
  ⟨fun _ f => if f then ⟨3, 1⟩ else ⟨1, 3⟩⟩

/-- Finite fixture likelihood scorer. -/
def ch13_likelihoodBool : Scorer Bool Bool :=
  ⟨fun _ f => if f then ⟨5, 1⟩ else ⟨1, 5⟩⟩

/-- Explicit checklist for the finite Bool fixture. -/
def ch13_checklistBool : PriorNBAssumptionChecklist Bool Bool Bool where
  inBin := fun g => g
  finitePool_nonempty := by decide
  localExchangeabilityInBin := True
  topK := 1
  topK_pos := by decide
  topK_le_pool := by decide
  surrogateCoverageObjective := True

def ch13_dependencyBool : Finset Bool := {true}

/-- Use pooled chapter-13 score as the Bayes surrogate on the worked fixture. -/
def ch13_etaBool : Bool → ℝ :=
  ch13ScorePooled ch13_globalPriorBool ch13_localPriorBool ch13_likelihoodBool true

def ch13_deltaZero : Bool → ℝ := fun _ => 0

lemma ch13_localExchangeabilityBool :
    ch13_checklistBool.localExchangeabilityInBin := by
  trivial

lemma ch13_pooledRankingBool :
    BayesOptimalRanking ch13_etaBool
      (ch13ScorePooled ch13_globalPriorBool ch13_localPriorBool ch13_likelihoodBool true) := by
  intro x y
  simp [ch13_etaBool]

lemma ch13_twoStageRankingBool :
    BayesOptimalRanking ch13_etaBool
      (ch13ScoreTwoStage ch13_globalPriorBool ch13_localPriorBool ch13_likelihoodBool true) := by
  have hSel :=
    ch13_selector_default_ranking_iff
      (A := ch13_checklistBool) (η := ch13_etaBool)
      (globalPrior := ch13_globalPriorBool) (localPrior := ch13_localPriorBool)
      (likelihood := ch13_likelihoodBool) (g := true)
      ch13_localExchangeabilityBool
  exact hSel.2.2.mp ch13_pooledRankingBool

lemma ch13_marginBool :
    ∀ x y, ch13_etaBool x < ch13_etaBool y →
      ch13ScorePooled ch13_globalPriorBool ch13_localPriorBool ch13_likelihoodBool true y
        - ch13ScorePooled ch13_globalPriorBool ch13_localPriorBool ch13_likelihoodBool true x
          > 2 * (0 : ℝ) := by
  intro x y hlt
  have hpos :
      ch13ScorePooled ch13_globalPriorBool ch13_localPriorBool ch13_likelihoodBool true y
        - ch13ScorePooled ch13_globalPriorBool ch13_localPriorBool ch13_likelihoodBool true x
          > 0 := by
    exact sub_pos.mpr (by simpa [ch13_etaBool] using hlt)
  simpa using hpos

/-- Worked Chapter-13 theorem:
explicit finite checklist + scorers imply the full algorithmic end-to-end guarantee. -/
theorem ch13_bool_end_to_end_algorithmic :
    let G := greedySelect ch13_dependencyBool ch13_checklistBool.topK
    ch13_checklistBool.topK ≤ Fintype.card Bool
      ∧ (∀ g' f',
          0 ≤ (selectorDefaults_halfGate Bool Bool).gate g' f'
            ∧ (selectorDefaults_halfGate Bool Bool).gate g' f' ≤ 1)
      ∧ BayesOptimalRanking ch13_etaBool
          (perturbedScore
            (ch13ScorePooled ch13_globalPriorBool ch13_localPriorBool ch13_likelihoodBool true)
            ch13_deltaZero)
      ∧ (1 - Real.exp (-1))
          * (Nat.min ch13_checklistBool.topK ch13_dependencyBool.card : ℝ)
          ≤ dependencyCoverage ch13_dependencyBool G := by
  simpa [ch13_deltaZero] using
    (ch13_inferenceControl_end_to_end_algorithmic
      (A := ch13_checklistBool) (η := ch13_etaBool)
      (globalPrior := ch13_globalPriorBool) (localPrior := ch13_localPriorBool)
      (likelihood := ch13_likelihoodBool) (g := true)
      ch13_localExchangeabilityBool
      (δ := ch13_deltaZero) (ε := 0)
      ch13_twoStageRankingBool
      (hbound := by intro x; simp [ch13_deltaZero])
      (hmargin := ch13_marginBool)
      (htie := by intro x y hxy; simp [ch13_deltaZero])
      (D := ch13_dependencyBool))

/-- Concrete coverage corollary on the fixture:
with one true dependency and `topK = 1`, the greedy selector covers it exactly. -/
theorem ch13_bool_coverage_exact_one :
    dependencyCoverage ch13_dependencyBool
      (greedySelect ch13_dependencyBool ch13_checklistBool.topK) = 1 := by
  have hchain :
      GreedyChain ch13_dependencyBool ch13_checklistBool.topK
        (greedySelect ch13_dependencyBool ch13_checklistBool.topK) :=
    greedySelect_chain_of_le_card
      (D := ch13_dependencyBool) (k := ch13_checklistBool.topK)
      ch13_checklistBool.topK_le_pool
  have hcov :
      dependencyCoverage ch13_dependencyBool
        (greedySelect ch13_dependencyBool ch13_checklistBool.topK)
        = Nat.min ch13_checklistBool.topK ch13_dependencyBool.card :=
    greedyChain_coverage_eq_min
      (D := ch13_dependencyBool)
      (S := greedySelect ch13_dependencyBool ch13_checklistBool.topK)
      (i := ch13_checklistBool.topK) hchain
  simpa [ch13_dependencyBool, ch13_checklistBool] using hcov

/-- Finite-3 fixture scorer emphasizing `{0,1}` over `2`. -/
def ch13_globalPriorFin3 : Scorer Unit (Fin 3) :=
  ⟨fun _ f => if f = (0 : Fin 3) ∨ f = (1 : Fin 3) then ⟨6, 1⟩ else ⟨1, 6⟩⟩

/-- Finite-3 local scorer, aligned with the same preference. -/
def ch13_localPriorFin3 : Scorer Unit (Fin 3) :=
  ⟨fun _ f => if f = (0 : Fin 3) ∨ f = (1 : Fin 3) then ⟨5, 1⟩ else ⟨1, 5⟩⟩

/-- Finite-3 likelihood scorer, aligned with the same preference. -/
def ch13_likelihoodFin3 : Scorer Unit (Fin 3) :=
  ⟨fun _ f => if f = (0 : Fin 3) ∨ f = (1 : Fin 3) then ⟨7, 1⟩ else ⟨1, 7⟩⟩

/-- Explicit `topK = 2` checklist on `Fin 3`. -/
def ch13_checklistFin3 : PriorNBAssumptionChecklist Unit (Fin 3) Unit where
  inBin := fun _ => ()
  finitePool_nonempty := by decide
  localExchangeabilityInBin := True
  topK := 2
  topK_pos := by decide
  topK_le_pool := by decide
  surrogateCoverageObjective := True

def ch13_dependencyFin3 : Finset (Fin 3) := ({0, 1} : Finset (Fin 3))

def ch13_etaFin3 : Fin 3 → ℝ :=
  ch13ScorePooled ch13_globalPriorFin3 ch13_localPriorFin3 ch13_likelihoodFin3 ()

def ch13_deltaZeroFin3 : Fin 3 → ℝ := fun _ => 0

lemma ch13_localExchangeabilityFin3 :
    ch13_checklistFin3.localExchangeabilityInBin := by
  trivial

lemma ch13_pooledRankingFin3 :
    BayesOptimalRanking ch13_etaFin3
      (ch13ScorePooled ch13_globalPriorFin3 ch13_localPriorFin3 ch13_likelihoodFin3 ()) := by
  intro x y
  simp [ch13_etaFin3]

lemma ch13_twoStageRankingFin3 :
    BayesOptimalRanking ch13_etaFin3
      (ch13ScoreTwoStage ch13_globalPriorFin3 ch13_localPriorFin3 ch13_likelihoodFin3 ()) := by
  have hSel :=
    ch13_selector_default_ranking_iff
      (A := ch13_checklistFin3) (η := ch13_etaFin3)
      (globalPrior := ch13_globalPriorFin3) (localPrior := ch13_localPriorFin3)
      (likelihood := ch13_likelihoodFin3) (g := ())
      ch13_localExchangeabilityFin3
  exact hSel.2.2.mp ch13_pooledRankingFin3

lemma ch13_marginFin3 :
    ∀ x y, ch13_etaFin3 x < ch13_etaFin3 y →
      ch13ScorePooled ch13_globalPriorFin3 ch13_localPriorFin3 ch13_likelihoodFin3 () y
        - ch13ScorePooled ch13_globalPriorFin3 ch13_localPriorFin3 ch13_likelihoodFin3 () x
          > 2 * (0 : ℝ) := by
  intro x y hlt
  have hpos :
      ch13ScorePooled ch13_globalPriorFin3 ch13_localPriorFin3 ch13_likelihoodFin3 () y
        - ch13ScorePooled ch13_globalPriorFin3 ch13_localPriorFin3 ch13_likelihoodFin3 () x
          > 0 := by
    exact sub_pos.mpr (by simpa [ch13_etaFin3] using hlt)
  simpa using hpos

/-- Worked Chapter-13 theorem with nontrivial budget `topK = 2`. -/
theorem ch13_fin3_end_to_end_algorithmic_topK2 :
    let G := greedySelect ch13_dependencyFin3 ch13_checklistFin3.topK
    ch13_checklistFin3.topK ≤ Fintype.card (Fin 3)
      ∧ (∀ g' f',
          0 ≤ (selectorDefaults_halfGate Unit (Fin 3)).gate g' f'
            ∧ (selectorDefaults_halfGate Unit (Fin 3)).gate g' f' ≤ 1)
      ∧ BayesOptimalRanking ch13_etaFin3
          (perturbedScore
            (ch13ScorePooled ch13_globalPriorFin3 ch13_localPriorFin3 ch13_likelihoodFin3 ())
            ch13_deltaZeroFin3)
      ∧ (1 - Real.exp (-1))
          * (Nat.min ch13_checklistFin3.topK ch13_dependencyFin3.card : ℝ)
          ≤ dependencyCoverage ch13_dependencyFin3 G := by
  simpa [ch13_deltaZeroFin3] using
    (ch13_inferenceControl_end_to_end_algorithmic
      (A := ch13_checklistFin3) (η := ch13_etaFin3)
      (globalPrior := ch13_globalPriorFin3) (localPrior := ch13_localPriorFin3)
      (likelihood := ch13_likelihoodFin3) (g := ())
      ch13_localExchangeabilityFin3
      (δ := ch13_deltaZeroFin3) (ε := 0)
      ch13_twoStageRankingFin3
      (hbound := by intro x; simp [ch13_deltaZeroFin3])
      (hmargin := ch13_marginFin3)
      (htie := by intro x y hxy; simp [ch13_deltaZeroFin3])
      (D := ch13_dependencyFin3))

/-- Concrete `topK = 2` coverage corollary on the `Fin 3` fixture. -/
theorem ch13_fin3_coverage_exact_two :
    dependencyCoverage ch13_dependencyFin3
      (greedySelect ch13_dependencyFin3 ch13_checklistFin3.topK) = 2 := by
  have hchain :
      GreedyChain ch13_dependencyFin3 ch13_checklistFin3.topK
        (greedySelect ch13_dependencyFin3 ch13_checklistFin3.topK) :=
    greedySelect_chain_of_le_card
      (D := ch13_dependencyFin3) (k := ch13_checklistFin3.topK)
      ch13_checklistFin3.topK_le_pool
  have hcov :
      dependencyCoverage ch13_dependencyFin3
        (greedySelect ch13_dependencyFin3 ch13_checklistFin3.topK)
        = Nat.min ch13_checklistFin3.topK ch13_dependencyFin3.card :=
    greedyChain_coverage_eq_min
      (D := ch13_dependencyFin3)
      (S := greedySelect ch13_dependencyFin3 ch13_checklistFin3.topK)
      (i := ch13_checklistFin3.topK) hchain
  simpa [ch13_checklistFin3, ch13_dependencyFin3] using hcov

end

end Mettapedia.Logic.PLNInferenceControlExamples
