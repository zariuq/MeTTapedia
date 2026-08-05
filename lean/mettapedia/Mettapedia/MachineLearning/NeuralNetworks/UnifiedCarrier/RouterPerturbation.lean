import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Routing stability under logit perturbations

A router winner can change under a uniformly small perturbation only when the
old noisy scores were near-tied.  This deterministic statement is the
load-bearing core behind probabilistic smooth-router bounds: a distributional
bound additionally requires an anti-concentration estimate for the near-tie
event.

The result is independent of how logits or routing noise are produced.  It can
therefore be reused for precision-biased reads, expert routing, and other
finite selection mechanisms without identifying their probability models.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace RouterPerturbation

variable {Expert Sample : Type*}

/-- A selected index attains the maximum score.  Ties are allowed. -/
def IsWinner (score : Expert → ℝ) (winner : Expert) : Prop :=
  ∀ expert, score expert ≤ score winner

/-- Two logit vectors differ by at most `budget` in every coordinate. -/
def UniformlyClose
    (oldLogit newLogit : Expert → ℝ) (budget : ℝ) : Prop :=
  ∀ expert, |newLogit expert - oldLogit expert| ≤ budget

/-- Routing scores add a fixed noise realization to the logits. -/
def noisyScore
    (logit noise : Expert → ℝ) (expert : Expert) : ℝ :=
  logit expert + noise expert

/-- A uniform logit perturbation can change the winner only across an old
pairwise score gap of at most twice the perturbation budget. -/
theorem winner_change_requires_near_tie
    {oldLogit newLogit noise : Expert → ℝ}
    {oldWinner newWinner : Expert} {budget : ℝ}
    (close : UniformlyClose oldLogit newLogit budget)
    (oldWins : IsWinner (noisyScore oldLogit noise) oldWinner)
    (newWins : IsWinner (noisyScore newLogit noise) newWinner) :
    |noisyScore oldLogit noise oldWinner -
        noisyScore oldLogit noise newWinner| ≤
      2 * budget := by
  have oldGapNonnegative :
      0 ≤ noisyScore oldLogit noise oldWinner -
        noisyScore oldLogit noise newWinner := by
    linarith [oldWins newWinner]
  have oldWinnerPerturbation :=
    (abs_le.mp (close oldWinner)).1
  have newWinnerPerturbation :=
    (abs_le.mp (close newWinner)).2
  have newWinnerOrder :
      noisyScore newLogit noise oldWinner ≤
        noisyScore newLogit noise newWinner :=
    newWins oldWinner
  rw [abs_of_nonneg oldGapNonnegative]
  change
    newLogit oldWinner + noise oldWinner ≤
      newLogit newWinner + noise newWinner at newWinnerOrder
  change
    oldLogit oldWinner + noise oldWinner -
        (oldLogit newWinner + noise newWinner) ≤
      2 * budget
  linarith

/-- A strict old-score margin exceeding twice the perturbation budget makes
the selected winner invariant under every admissible perturbation. -/
theorem winner_stable_of_strict_margin
    [DecidableEq Expert]
    {oldLogit newLogit noise : Expert → ℝ}
    {oldWinner newWinner : Expert} {budget margin : ℝ}
    (close : UniformlyClose oldLogit newLogit budget)
    (oldWins : IsWinner (noisyScore oldLogit noise) oldWinner)
    (newWins : IsWinner (noisyScore newLogit noise) newWinner)
    (strictMargin :
      ∀ expert, expert ≠ oldWinner →
        noisyScore oldLogit noise expert + margin ≤
          noisyScore oldLogit noise oldWinner)
    (marginDominates : 2 * budget < margin) :
    newWinner = oldWinner := by
  by_contra different
  have nearTie :=
    winner_change_requires_near_tie close oldWins newWins
  have oldGapNonnegative :
      0 ≤ noisyScore oldLogit noise oldWinner -
        noisyScore oldLogit noise newWinner := by
    linarith [oldWins newWinner]
  rw [abs_of_nonneg oldGapNonnegative] at nearTie
  have marginBound := strictMargin newWinner different
  linarith

section FiniteSamples

variable [Fintype Sample] [DecidableEq Expert]

/-- Samples on which two routing rules select different experts. -/
def disagreementSet
    (oldRoute newRoute : Sample → Expert) : Finset Sample :=
  Finset.univ.filter fun sample => oldRoute sample ≠ newRoute sample

/-- Samples whose selected old/new expert pair was within the deterministic
near-tie band under the old scores. -/
noncomputable def nearTieSet
    (oldLogit : Expert → ℝ)
    (noise : Sample → Expert → ℝ)
    (oldRoute newRoute : Sample → Expert)
    (budget : ℝ) : Finset Sample :=
  Finset.univ.filter fun sample =>
    |noisyScore oldLogit (noise sample) (oldRoute sample) -
        noisyScore oldLogit (noise sample) (newRoute sample)| ≤
      2 * budget

/-- Every empirical route disagreement lies in the corresponding near-tie
event.  The theorem deliberately leaves any anti-concentration bound on that
event as a separate distributional premise. -/
theorem disagreementSet_subset_nearTieSet
    {oldLogit newLogit : Expert → ℝ}
    {noise : Sample → Expert → ℝ}
    {oldRoute newRoute : Sample → Expert}
    {budget : ℝ}
    (close : UniformlyClose oldLogit newLogit budget)
    (oldWins :
      ∀ sample,
        IsWinner (noisyScore oldLogit (noise sample)) (oldRoute sample))
    (newWins :
      ∀ sample,
        IsWinner (noisyScore newLogit (noise sample)) (newRoute sample)) :
    disagreementSet oldRoute newRoute ⊆
      nearTieSet oldLogit noise oldRoute newRoute budget := by
  intro sample inDisagreement
  simp only [disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    at inDisagreement
  simp only [nearTieSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact winner_change_requires_near_tie
    close (oldWins sample) (newWins sample)

/-- Finite empirical disagreement is bounded by near-tie frequency. -/
theorem disagreement_card_le_nearTie_card
    {oldLogit newLogit : Expert → ℝ}
    {noise : Sample → Expert → ℝ}
    {oldRoute newRoute : Sample → Expert}
    {budget : ℝ}
    (close : UniformlyClose oldLogit newLogit budget)
    (oldWins :
      ∀ sample,
        IsWinner (noisyScore oldLogit (noise sample)) (oldRoute sample))
    (newWins :
      ∀ sample,
        IsWinner (noisyScore newLogit (noise sample)) (newRoute sample)) :
    (disagreementSet oldRoute newRoute).card ≤
      (nearTieSet oldLogit noise oldRoute newRoute budget).card :=
  Finset.card_le_card
    (disagreementSet_subset_nearTieSet close oldWins newWins)

end FiniteSamples

/-! ## Positive and negative fixtures -/

noncomputable def stableOldLogit : Fin 2 → ℝ := ![3, 0]
noncomputable def stableNewLogit : Fin 2 → ℝ := ![5 / 2, 1 / 2]
noncomputable def zeroNoise : Fin 2 → ℝ := ![0, 0]

theorem stableLogits_close :
    UniformlyClose stableOldLogit stableNewLogit (1 / 2) := by
  intro expert
  fin_cases expert <;>
    norm_num [UniformlyClose, stableOldLogit, stableNewLogit]

theorem stableOldWinner :
    IsWinner (noisyScore stableOldLogit zeroNoise) 0 := by
  intro expert
  fin_cases expert <;>
    norm_num [IsWinner, noisyScore, stableOldLogit, zeroNoise]

theorem stableNewWinner :
    IsWinner (noisyScore stableNewLogit zeroNoise) 0 := by
  intro expert
  fin_cases expert <;>
    norm_num [IsWinner, noisyScore, stableNewLogit, zeroNoise]

theorem stableWinner_is_preserved
    (newWinner : Fin 2)
    (newWins : IsWinner (noisyScore stableNewLogit zeroNoise) newWinner) :
    newWinner = 0 := by
  apply winner_stable_of_strict_margin (budget := 1 / 2) (margin := 2)
    stableLogits_close stableOldWinner newWins
  · intro expert different
    fin_cases expert
    · exact (different rfl).elim
    · norm_num [noisyScore, stableOldLogit, zeroNoise]
  · norm_num

noncomputable def nearTieOldLogit : Fin 2 → ℝ := ![1 / 10, 0]
noncomputable def nearTieNewLogit : Fin 2 → ℝ := ![0, 1 / 10]

theorem nearTieLogits_close :
    UniformlyClose nearTieOldLogit nearTieNewLogit (1 / 10) := by
  intro expert
  fin_cases expert <;>
    norm_num [UniformlyClose, nearTieOldLogit, nearTieNewLogit]

theorem nearTieOldWinner :
    IsWinner (noisyScore nearTieOldLogit zeroNoise) 0 := by
  intro expert
  fin_cases expert <;>
    norm_num [IsWinner, noisyScore, nearTieOldLogit, zeroNoise]

theorem nearTieNewWinner :
    IsWinner (noisyScore nearTieNewLogit zeroNoise) 1 := by
  intro expert
  fin_cases expert <;>
    norm_num [IsWinner, noisyScore, nearTieNewLogit, zeroNoise]

/-- Without a margin larger than twice the perturbation budget, the selected
expert can genuinely change. -/
theorem nearTie_perturbation_changes_winner :
    IsWinner (noisyScore nearTieOldLogit zeroNoise) 0 ∧
      IsWinner (noisyScore nearTieNewLogit zeroNoise) 1 ∧
      (0 : Fin 2) ≠ 1 :=
  ⟨nearTieOldWinner, nearTieNewWinner, by decide⟩

#print axioms winner_change_requires_near_tie
#print axioms winner_stable_of_strict_margin
#print axioms disagreement_card_le_nearTie_card
#print axioms stableWinner_is_preserved
#print axioms nearTie_perturbation_changes_winner

end RouterPerturbation

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
