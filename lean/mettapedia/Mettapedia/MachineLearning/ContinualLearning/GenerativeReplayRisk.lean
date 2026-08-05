import Mathlib

/-!
# Generative-replay risk decomposition

Shin et al., *Continual Learning with Deep Generative Replay*
(NeurIPS 2017, arXiv:1705.08690), train a new solver on a mixture of current
labelled data and generated past inputs labelled by the previous solver
(Equation 1).  Evaluation instead uses the corresponding mixture with true
past labels (Equation 2).  The source says that replay becomes equivalent to
joint training when the generator recovers the past input distribution.

This file isolates the two independent gaps hidden by that statement.
The train--test risk difference is exactly the retained old-data weight times
the sum of a generator-distribution gap and a teacher-target gap.  A perfect
generator removes only the first term.  Equivalence to true-label joint risk
still requires the old solver's distillation targets to agree at the risk
level, unless the two errors happen to cancel.

The algebra is agnostic to the generator and solver classes and therefore
applies to any expectations for which the declared scalar risks exist.  It
does not prove distributional convergence of a GAN, teacher calibration,
optimization convergence, privacy, or benchmark retention.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace GenerativeReplayRisk

/-! ## Source-shaped mixture risks -/

/-- Mixture of a current-task risk and an old-task risk, with current-task
fraction `currentFraction`. -/
def mixtureRisk
    (currentFraction currentRisk oldRisk : ℝ) : ℝ :=
  currentFraction * currentRisk +
    (1 - currentFraction) * oldRisk

/-- Equation 1 after taking expectations: old inputs come from the generator
and their targets come from the previous solver. -/
def replayTrainRisk
    (currentFraction currentRisk generatedTeacherRisk : ℝ) : ℝ :=
  mixtureRisk currentFraction currentRisk generatedTeacherRisk

/-- Equation 2: old inputs and targets come from the true past distribution. -/
def jointTestRisk
    (currentFraction currentRisk pastTrueRisk : ℝ) : ℝ :=
  mixtureRisk currentFraction currentRisk pastTrueRisk

/-! ## Distribution and target gaps -/

/-- Exact two-gap decomposition.  `generatedTeacherRisk - pastTeacherRisk`
measures generator-distribution error under the fixed old solver, while
`pastTeacherRisk - pastTrueRisk` measures target substitution on the true
past distribution. -/
theorem replayTrainRisk_sub_jointTestRisk
    (currentFraction currentRisk generatedTeacherRisk
      pastTeacherRisk pastTrueRisk : ℝ) :
    replayTrainRisk currentFraction currentRisk generatedTeacherRisk -
        jointTestRisk currentFraction currentRisk pastTrueRisk =
      (1 - currentFraction) *
        ((generatedTeacherRisk - pastTeacherRisk) +
          (pastTeacherRisk - pastTrueRisk)) := by
  simp [replayTrainRisk, jointTestRisk, mixtureRisk]
  ring

/-- Risk-level recovery of the past input distribution removes the generator
term but leaves the teacher-target term. -/
theorem perfectGenerator_replayTrainRisk_sub_jointTestRisk
    (currentFraction currentRisk pastTeacherRisk pastTrueRisk : ℝ) :
    replayTrainRisk currentFraction currentRisk pastTeacherRisk -
        jointTestRisk currentFraction currentRisk pastTrueRisk =
      (1 - currentFraction) *
        (pastTeacherRisk - pastTrueRisk) := by
  rw [replayTrainRisk_sub_jointTestRisk
    currentFraction currentRisk pastTeacherRisk
    pastTeacherRisk pastTrueRisk]
  ring

/-- Before the all-current-data endpoint, a perfect generator yields exact
joint risk if and only if the old solver's targets agree with true labels at
the risk level. -/
theorem perfectGenerator_train_eq_test_iff_teacherRisk_eq
    {currentFraction currentRisk pastTeacherRisk pastTrueRisk : ℝ}
    (not_all_current : currentFraction < 1) :
    replayTrainRisk currentFraction currentRisk pastTeacherRisk =
        jointTestRisk currentFraction currentRisk pastTrueRisk ↔
      pastTeacherRisk = pastTrueRisk := by
  have retained_positive : 0 < 1 - currentFraction :=
    sub_pos.mpr not_all_current
  constructor
  · intro risks_equal
    have gap_zero :
        replayTrainRisk currentFraction currentRisk pastTeacherRisk -
            jointTestRisk currentFraction currentRisk pastTrueRisk = 0 :=
      sub_eq_zero.mpr risks_equal
    rw [perfectGenerator_replayTrainRisk_sub_jointTestRisk] at gap_zero
    nlinarith
  · intro teacher_exact
    subst pastTrueRisk
    simp [replayTrainRisk, jointTestRisk]

/-- Exact generator and exact teacher targets are sufficient for equality with
the true-label joint risk. -/
theorem exactGenerator_exactTeacher_replay_eq_joint
    {currentFraction currentRisk generatedTeacherRisk
      pastTeacherRisk pastTrueRisk : ℝ}
    (generator_exact : generatedTeacherRisk = pastTeacherRisk)
    (teacher_exact : pastTeacherRisk = pastTrueRisk) :
    replayTrainRisk currentFraction currentRisk generatedTeacherRisk =
      jointTestRisk currentFraction currentRisk pastTrueRisk := by
  subst generatedTeacherRisk
  subst pastTeacherRisk
  simp [replayTrainRisk, jointTestRisk]

/-- An absolute generator-plus-teacher error budget controls the complete
train--test risk gap whenever the old-data mixture weight is nonnegative. -/
theorem abs_replayTrainRisk_sub_jointTestRisk_le
    {currentFraction currentRisk generatedTeacherRisk
      pastTeacherRisk pastTrueRisk : ℝ}
    (fraction_at_most_one : currentFraction ≤ 1) :
    |replayTrainRisk currentFraction currentRisk generatedTeacherRisk -
        jointTestRisk currentFraction currentRisk pastTrueRisk| ≤
      (1 - currentFraction) *
        (|generatedTeacherRisk - pastTeacherRisk| +
          |pastTeacherRisk - pastTrueRisk|) := by
  rw [replayTrainRisk_sub_jointTestRisk, abs_mul,
    abs_of_nonneg (sub_nonneg.mpr fraction_at_most_one)]
  exact mul_le_mul_of_nonneg_left
    (abs_add_le _ _) (sub_nonneg.mpr fraction_at_most_one)

/-! ## Executable boundaries -/

/-- Perfect input-distribution replay alone does not recover true-label joint
training when the old solver supplies different targets. -/
theorem perfectGenerator_teacherMismatch_not_joint :
    replayTrainRisk ((1 : ℝ) / 2) 0 0 = 0 ∧
      jointTestRisk ((1 : ℝ) / 2) 0 2 = 1 ∧
      replayTrainRisk ((1 : ℝ) / 2) 0 0 ≠
        jointTestRisk ((1 : ℝ) / 2) 0 2 := by
  norm_num [replayTrainRisk, jointTestRisk, mixtureRisk]

/-- Exact generator and teacher risks recover a nontrivial mixed joint risk. -/
theorem exactReplay :
    replayTrainRisk ((1 : ℝ) / 3) 3 6 = 5 ∧
      jointTestRisk ((1 : ℝ) / 3) 3 6 = 5 := by
  norm_num [replayTrainRisk, jointTestRisk, mixtureRisk]

/-- Generator and teacher errors can cancel, so exactness of each component is
sufficient but not necessary for equality of aggregate risks. -/
theorem generator_teacher_error_cancellation :
    replayTrainRisk ((1 : ℝ) / 2) 0 2 =
        jointTestRisk ((1 : ℝ) / 2) 0 2 ∧
      (2 : ℝ) ≠ 1 ∧
      (1 : ℝ) ≠ 2 := by
  norm_num [replayTrainRisk, jointTestRisk, mixtureRisk]

end GenerativeReplayRisk

end Mettapedia.MachineLearning.ContinualLearning
