import Mathlib.Tactic

/-!
# Maximally interfered retrieval

Aljundi et al. (2019), *Online Continual Learning with Maximally Interfered
Retrieval*, rank replay candidates by the increase in their loss after a
virtual update on the incoming batch.  Their first memory criterion is

`loss candidate virtualParameter - loss candidate currentParameter`.

Their second criterion replaces the current baseline by the smaller of the
current loss and the best previously recorded loss.

This file formalizes the exact finite-step score and its relationship to
gradient interference in the scalar quadratic model.  The score is the
negative gradient-alignment term plus an explicit curvature remainder.
Conflicting gradients therefore cause positive interference for every
nonnegative step and convex replay loss, but compatible gradients can still
be harmed by an oversized virtual step.  A two-candidate fixture further
shows that ranking by gradient conflict alone can disagree with the source's
finite-loss ranking.

The results justify logging both alignment and finite virtual loss.  They do
not prove that replaying a selected example improves future retention, that a
finite buffer represents the past, or that a generator produces valid
examples.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace MaximallyInterferedRetrieval

noncomputable section

/-- The parameter obtained by the source's hypothetical update on the incoming
batch. -/
def virtualParameter
    (parameter step incomingGradient : ℝ) : ℝ :=
  parameter - step * incomingGradient

/-- MIR's first memory score: finite replay-loss change under the virtual
incoming update. -/
def interferenceScore
    (loss : ℝ → ℝ)
    (parameter step incomingGradient : ℝ) : ℝ :=
  loss (virtualParameter parameter step incomingGradient) -
    loss parameter

/-- Scalar convex quadratic replay loss, sufficient to expose the exact
finite-step geometry. -/
def quadraticLoss
    (curvature optimum parameter : ℝ) : ℝ :=
  curvature / 2 * (parameter - optimum) ^ 2

def quadraticGradient
    (curvature optimum parameter : ℝ) : ℝ :=
  curvature * (parameter - optimum)

/-- Exact source-score expansion: finite interference is negative
gradient alignment plus a second-order replay-curvature term. -/
theorem quadratic_interferenceScore_exact
    (curvature optimum parameter step incomingGradient : ℝ) :
    interferenceScore
        (quadraticLoss curvature optimum)
        parameter step incomingGradient =
      -step * incomingGradient *
          quadraticGradient curvature optimum parameter +
        step ^ 2 * curvature / 2 * incomingGradient ^ 2 := by
  simp [interferenceScore, virtualParameter, quadraticLoss,
    quadraticGradient]
  ring

/-- The finite-score error of the first-order alignment approximation is
exactly the quadratic curvature remainder. -/
theorem quadratic_interferenceScore_sub_firstOrder
    (curvature optimum parameter step incomingGradient : ℝ) :
    interferenceScore
          (quadraticLoss curvature optimum)
          parameter step incomingGradient -
        (-step * incomingGradient *
          quadraticGradient curvature optimum parameter) =
      step ^ 2 * curvature / 2 * incomingGradient ^ 2 := by
  rw [quadratic_interferenceScore_exact]
  ring

/-- Under convex replay curvature, the first-order approximation error is
nonnegative. -/
theorem quadratic_firstOrder_le_interferenceScore
    (curvature optimum parameter step incomingGradient : ℝ)
    (convex : 0 ≤ curvature) :
    -step * incomingGradient *
          quadraticGradient curvature optimum parameter ≤
      interferenceScore
        (quadraticLoss curvature optimum)
        parameter step incomingGradient := by
  rw [quadratic_interferenceScore_exact]
  have remainderNonnegative :
      0 ≤ step ^ 2 * curvature / 2 * incomingGradient ^ 2 := by
    positivity
  linarith

/-- The absolute error has an exact computable budget under convex
curvature. -/
theorem abs_quadratic_interferenceScore_sub_firstOrder
    (curvature optimum parameter step incomingGradient : ℝ)
    (convex : 0 ≤ curvature) :
    |interferenceScore
          (quadraticLoss curvature optimum)
          parameter step incomingGradient -
        (-step * incomingGradient *
          quadraticGradient curvature optimum parameter)| =
      step ^ 2 * curvature / 2 * incomingGradient ^ 2 := by
  rw [quadratic_interferenceScore_sub_firstOrder]
  rw [abs_of_nonneg]
  positivity

/-- A positive step and negatively aligned replay gradient produce strictly
positive finite interference for every convex quadratic replay loss. -/
theorem quadratic_conflict_implies_positive_interference
    (curvature optimum parameter step incomingGradient : ℝ)
    (stepPositive : 0 < step)
    (convex : 0 ≤ curvature)
    (conflict :
      incomingGradient *
          quadraticGradient curvature optimum parameter < 0) :
    0 <
      interferenceScore
        (quadraticLoss curvature optimum)
        parameter step incomingGradient := by
  rw [quadratic_interferenceScore_exact]
  have firstPositive :
      0 <
        -step * incomingGradient *
          quadraticGradient curvature optimum parameter := by
    nlinarith
  have remainderNonnegative :
      0 ≤ step ^ 2 * curvature / 2 * incomingGradient ^ 2 := by
    positivity
  linarith

/-- Compatible first-order gradients are safe only when their margin covers
the finite curvature remainder. -/
theorem quadratic_nonincrease_of_alignment_budget
    (curvature optimum parameter step incomingGradient : ℝ)
    (budget :
      step ^ 2 * curvature / 2 * incomingGradient ^ 2 ≤
        step * incomingGradient *
          quadraticGradient curvature optimum parameter) :
    interferenceScore
        (quadraticLoss curvature optimum)
        parameter step incomingGradient ≤ 0 := by
  rw [quadratic_interferenceScore_exact]
  linarith

/-! ## The historical-best baseline -/

/-- MIR's second score uses the best of the current and recorded historical
loss as its baseline. -/
def historicalInterferenceScore
    (virtualLoss currentLoss bestRecordedLoss : ℝ) : ℝ :=
  virtualLoss - min currentLoss bestRecordedLoss

/-- The historical score is the current-baseline score plus the exact
baseline regret. -/
theorem historicalInterferenceScore_eq_current_add_regret
    (virtualLoss currentLoss bestRecordedLoss : ℝ) :
    historicalInterferenceScore
        virtualLoss currentLoss bestRecordedLoss =
      (virtualLoss - currentLoss) +
        (currentLoss - min currentLoss bestRecordedLoss) := by
  simp [historicalInterferenceScore]

/-- Replacing the baseline by its historical minimum can only increase the
retrieval score. -/
theorem currentScore_le_historicalInterferenceScore
    (virtualLoss currentLoss bestRecordedLoss : ℝ) :
    virtualLoss - currentLoss ≤
      historicalInterferenceScore
        virtualLoss currentLoss bestRecordedLoss := by
  rw [historicalInterferenceScore_eq_current_add_regret]
  have baseline := min_le_left currentLoss bestRecordedLoss
  linarith

/-- The two source criteria coincide when the current loss is already no
worse than the stored historical value. -/
theorem historicalInterferenceScore_eq_current_of_le
    (virtualLoss currentLoss bestRecordedLoss : ℝ)
    (currentBest : currentLoss ≤ bestRecordedLoss) :
    historicalInterferenceScore
        virtualLoss currentLoss bestRecordedLoss =
      virtualLoss - currentLoss := by
  simp [historicalInterferenceScore, min_eq_left currentBest]

/-! ## Executable finite-step boundaries -/

/-- Aligned gradients can nevertheless increase replay loss when the virtual
step overshoots. -/
theorem aligned_gradients_can_have_positive_interference :
    quadraticGradient 1 0 1 = 1 ∧
      (1 : ℝ) * quadraticGradient 1 0 1 > 0 ∧
      interferenceScore (quadraticLoss 1 0) 1 3 1 = 3 / 2 := by
  norm_num [quadraticGradient, interferenceScore, quadraticLoss,
    virtualParameter]

/-- A candidate with weaker gradient conflict but larger curvature can have
the larger exact MIR score.  Thus first-order conflict and finite-loss
ranking are not interchangeable. -/
theorem curvature_can_reverse_gradientConflict_ranking :
    let incomingGradient : ℝ := 1
    let firstLoss := quadraticLoss 1 2
    let secondLoss := quadraticLoss 10 (1 / 10)
    quadraticGradient 1 2 0 = -2 ∧
      quadraticGradient 10 (1 / 10) 0 = -1 ∧
      interferenceScore firstLoss 0 1 incomingGradient = 5 / 2 ∧
      interferenceScore secondLoss 0 1 incomingGradient = 6 ∧
      interferenceScore firstLoss 0 1 incomingGradient <
        interferenceScore secondLoss 0 1 incomingGradient := by
  norm_num [quadraticGradient, interferenceScore, quadraticLoss,
    virtualParameter]

/-- The historical-best criterion can rank an example as more interfered
solely because it has already forgotten relative to its best recorded loss. -/
theorem historical_baseline_adds_regret :
    historicalInterferenceScore 7 6 2 = 5 ∧
      7 - 6 = 1 := by
  norm_num [historicalInterferenceScore]

#print axioms quadratic_interferenceScore_exact
#print axioms abs_quadratic_interferenceScore_sub_firstOrder
#print axioms quadratic_conflict_implies_positive_interference
#print axioms quadratic_nonincrease_of_alignment_budget
#print axioms historicalInterferenceScore_eq_current_add_regret
#print axioms currentScore_le_historicalInterferenceScore
#print axioms aligned_gradients_can_have_positive_interference
#print axioms curvature_can_reverse_gradientConflict_ranking

end

end MaximallyInterferedRetrieval

end Mettapedia.MachineLearning.ContinualLearning
