import Mathlib

/-!
# Replay-memory economics in an overparameterized linear model

Banayeeanzade, Soltanolkotabi, and Mirzasoleiman,
*Theoretical Insights into Overparameterized Models in Multi-Task and
Replay-Based Continual Learning* (TMLR 2025, arXiv:2408.16939), Theorem 4.1,
Equation (18), give a closed form for expected forgetting under pure replay in
a two-task noiseless Gaussian linear model.

This file takes that displayed closed form as a finite real-valued object and
derives a reusable consequence that is not stated explicitly in the source:
an exact threshold deciding whether one additional replay sample improves or
worsens the expected-forgetting expression.  The result separates the benefit
of retaining the old task from the interference caused by task dissimilarity.

The source's random-matrix expectation theorem is not reproved here.  In
particular, these results do not establish its Gaussian-design hypotheses, do
not transfer the formula to nonlinear networks, and do not make an empirical
claim about a replay implementation.  They certify the algebra and ordering of
the source formula within its positive-denominator regime.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ReplayMemoryEconomics

noncomputable section

/-- Remaining overparameterization after the current task, replay memory, and
the source formula's one-dimensional margin are removed. -/
def replaySlack (parameters taskSamples memorySamples : ℝ) : ℝ :=
  parameters - (taskSamples + memorySamples) - 1

/-- The expected-forgetting closed form from Theorem 4.1, Equation (18).

`taskGapSq` represents `‖w₁⋆ - w₂⋆‖²` and `oldTaskNormSq` represents
`‖w₁⋆‖²`.  Their nonnegativity belongs to the source interpretation; the
algebraic theorems below are stated over arbitrary reals unless a sign is
needed. -/
def pureReplayForgettingClosedForm
    (parameters taskSamples memorySamples
      taskGapSq oldTaskNormSq : ℝ) : ℝ :=
  taskSamples / parameters *
      (1 + memorySamples /
        replaySlack parameters taskSamples memorySamples) *
      taskGapSq -
    memorySamples / parameters * oldTaskNormSq

/-- Numerator governing the effect of adding one replay sample. -/
def replayMemoryIncrementNumerator
    (parameters taskSamples memorySamples
      taskGapSq oldTaskNormSq : ℝ) : ℝ :=
  taskSamples * (parameters - taskSamples - 1) * taskGapSq -
    oldTaskNormSq *
      replaySlack parameters taskSamples memorySamples *
      (replaySlack parameters taskSamples memorySamples - 1)

/-- With no replay memory, the source expression reduces to the
task-dissimilarity term alone. -/
theorem pureReplayForgettingClosedForm_zero_memory
    (parameters taskSamples taskGapSq oldTaskNormSq : ℝ) :
    pureReplayForgettingClosedForm parameters taskSamples 0
        taskGapSq oldTaskNormSq =
      taskSamples / parameters * taskGapSq := by
  simp [pureReplayForgettingClosedForm]

/-- Exact one-sample increment of the pure-replay forgetting expression.

The two nonzero slack hypotheses are precisely the denominators used before
and after adding one replay sample. -/
theorem pureReplayForgettingClosedForm_memoryStep_difference
    (parameters taskSamples memorySamples taskGapSq oldTaskNormSq : ℝ)
    (parameters_ne_zero : parameters ≠ 0)
    (slack_ne_zero :
      replaySlack parameters taskSamples memorySamples ≠ 0)
    (nextSlack_ne_zero :
      replaySlack parameters taskSamples memorySamples - 1 ≠ 0) :
    pureReplayForgettingClosedForm parameters taskSamples
          (memorySamples + 1) taskGapSq oldTaskNormSq -
        pureReplayForgettingClosedForm parameters taskSamples
          memorySamples taskGapSq oldTaskNormSq =
      replayMemoryIncrementNumerator parameters taskSamples memorySamples
          taskGapSq oldTaskNormSq /
        (parameters *
          replaySlack parameters taskSamples memorySamples *
          (replaySlack parameters taskSamples memorySamples - 1)) := by
  let slack := replaySlack parameters taskSamples memorySamples
  have nextSlack :
      replaySlack parameters taskSamples (memorySamples + 1) =
        slack - 1 := by
    dsimp [slack, replaySlack]
    ring
  have slack_ne_zero' : slack ≠ 0 := by
    simpa [slack] using slack_ne_zero
  have nextSlack_ne_zero' : slack - 1 ≠ 0 := by
    simpa [slack] using nextSlack_ne_zero
  unfold pureReplayForgettingClosedForm
  rw [nextSlack]
  unfold replayMemoryIncrementNumerator
  change
    taskSamples / parameters *
          (1 + (memorySamples + 1) / (slack - 1)) * taskGapSq -
        (memorySamples + 1) / parameters * oldTaskNormSq -
        (taskSamples / parameters *
            (1 + memorySamples / slack) * taskGapSq -
          memorySamples / parameters * oldTaskNormSq) =
      (taskSamples * (parameters - taskSamples - 1) * taskGapSq -
          oldTaskNormSq * slack * (slack - 1)) /
        (parameters * slack * (slack - 1))
  field_simp [parameters_ne_zero, slack_ne_zero', nextSlack_ne_zero']
  dsimp [slack, replaySlack]
  ring

/-- In the source's positive-denominator regime, adding one replay sample
strictly improves the expected-forgetting expression exactly when the
old-task retention term dominates the task-dissimilarity term. -/
theorem pureReplayForgettingClosedForm_add_memory_lt_iff
    (parameters taskSamples memorySamples taskGapSq oldTaskNormSq : ℝ)
    (parameters_pos : 0 < parameters)
    (slack_gt_one :
      1 < replaySlack parameters taskSamples memorySamples) :
    pureReplayForgettingClosedForm parameters taskSamples
          (memorySamples + 1) taskGapSq oldTaskNormSq <
        pureReplayForgettingClosedForm parameters taskSamples
          memorySamples taskGapSq oldTaskNormSq ↔
      taskSamples * (parameters - taskSamples - 1) * taskGapSq <
        oldTaskNormSq *
          replaySlack parameters taskSamples memorySamples *
          (replaySlack parameters taskSamples memorySamples - 1) := by
  have slack_pos :
      0 < replaySlack parameters taskSamples memorySamples := by
    linarith
  have nextSlack_pos :
      0 < replaySlack parameters taskSamples memorySamples - 1 := by
    linarith
  have denominator_pos :
      0 <
        parameters *
          replaySlack parameters taskSamples memorySamples *
          (replaySlack parameters taskSamples memorySamples - 1) := by
    positivity
  have difference :=
    pureReplayForgettingClosedForm_memoryStep_difference
      parameters taskSamples memorySamples taskGapSq oldTaskNormSq
      parameters_pos.ne' slack_pos.ne' nextSlack_pos.ne'
  rw [← sub_lt_zero]
  rw [difference]
  rw [div_lt_iff₀ denominator_pos]
  simp only [zero_mul]
  unfold replayMemoryIncrementNumerator
  exact sub_lt_zero

/-- The complementary strict boundary: in the same regime, one additional
sample worsens the expression exactly when task dissimilarity dominates. -/
theorem pureReplayForgettingClosedForm_lt_add_memory_iff
    (parameters taskSamples memorySamples taskGapSq oldTaskNormSq : ℝ)
    (parameters_pos : 0 < parameters)
    (slack_gt_one :
      1 < replaySlack parameters taskSamples memorySamples) :
    pureReplayForgettingClosedForm parameters taskSamples
          memorySamples taskGapSq oldTaskNormSq <
        pureReplayForgettingClosedForm parameters taskSamples
          (memorySamples + 1) taskGapSq oldTaskNormSq ↔
      oldTaskNormSq *
          replaySlack parameters taskSamples memorySamples *
          (replaySlack parameters taskSamples memorySamples - 1) <
        taskSamples * (parameters - taskSamples - 1) * taskGapSq := by
  have slack_pos :
      0 < replaySlack parameters taskSamples memorySamples := by
    linarith
  have nextSlack_pos :
      0 < replaySlack parameters taskSamples memorySamples - 1 := by
    linarith
  have denominator_pos :
      0 <
        parameters *
          replaySlack parameters taskSamples memorySamples *
          (replaySlack parameters taskSamples memorySamples - 1) := by
    positivity
  have difference :=
    pureReplayForgettingClosedForm_memoryStep_difference
      parameters taskSamples memorySamples taskGapSq oldTaskNormSq
      parameters_pos.ne' slack_pos.ne' nextSlack_pos.ne'
  rw [← sub_pos]
  rw [difference]
  rw [div_pos_iff]
  simp only [denominator_pos, and_true,
    not_lt_of_ge denominator_pos.le, and_false, or_false]
  unfold replayMemoryIncrementNumerator
  exact sub_pos

/-! ## Executable improvement and worsening fixtures -/

/-- At moderate task separation, increasing replay memory from one to two
samples strictly improves the source expression. -/
theorem moderate_task_gap_extra_memory_improves :
    pureReplayForgettingClosedForm 10 2 2 1 1 <
      pureReplayForgettingClosedForm 10 2 1 1 1 := by
  norm_num [pureReplayForgettingClosedForm, replaySlack]

/-- Exact values for the improving fixture. -/
theorem moderate_task_gap_fixture_values :
    pureReplayForgettingClosedForm 10 2 1 1 1 = 2 / 15 ∧
      pureReplayForgettingClosedForm 10 2 2 1 1 = 2 / 25 := by
  norm_num [pureReplayForgettingClosedForm, replaySlack]

/-- At larger task separation, the same additional replay sample strictly
worsens the source expression.  More memory is therefore not monotonically
beneficial under the closed form. -/
theorem large_task_gap_extra_memory_worsens :
    pureReplayForgettingClosedForm 10 2 1 3 1 <
      pureReplayForgettingClosedForm 10 2 2 3 1 := by
  norm_num [pureReplayForgettingClosedForm, replaySlack]

/-- Exact values for the worsening fixture. -/
theorem large_task_gap_fixture_values :
    pureReplayForgettingClosedForm 10 2 1 3 1 = 3 / 5 ∧
      pureReplayForgettingClosedForm 10 2 2 3 1 = 16 / 25 := by
  norm_num [pureReplayForgettingClosedForm, replaySlack]

#print axioms pureReplayForgettingClosedForm_memoryStep_difference
#print axioms pureReplayForgettingClosedForm_add_memory_lt_iff
#print axioms pureReplayForgettingClosedForm_lt_add_memory_iff
#print axioms moderate_task_gap_extra_memory_improves
#print axioms large_task_gap_extra_memory_worsens

end

end ReplayMemoryEconomics

end Mettapedia.MachineLearning.ContinualLearning
