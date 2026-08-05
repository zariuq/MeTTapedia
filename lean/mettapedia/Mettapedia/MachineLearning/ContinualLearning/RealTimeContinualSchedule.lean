import Mathlib.Tactic

/-!
# Work-rate schedules for real-time continual evaluation

Ghunaim et al., *Real-Time Evaluation in Online Continual Learning: A New
Hope* (CVPR 2023, arXiv:2302.01047), Section 3.2, evaluate a continual learner
against a stream that does not pause while training finishes. A method whose
update is more expensive than one stream interval completes fewer updates and
therefore predicts with an older parameter state.

The source reports rational stream-model relative complexities, including
`4/3` and `5/2`. This file represents such a rate by integer work units:
after `steps` stream arrivals, `steps * streamWork` units are available and
each model update consumes `methodWork` units. The greatest affordable number
of completed updates is their quotient. We prove exact work conservation,
maximality, bounded residual work, and the no-faster-than-stream update bound.

The source table is recovered exactly on a common 60-step horizon:

* complexity `1` completes 60 updates;
* `4/3` completes 45;
* `2` completes 30;
* `5/2` completes 24;
* `3` completes 20;
* `6` completes 10.

Rounding `4/3` down to integer complexity one would incorrectly allocate 60
updates instead of 45. A zero method-work fixture records the totalized
division boundary and justifies the positive-work premise.

This is a scheduling theorem only. FLOP estimates, asynchronous execution,
which arriving batch is consumed, prediction accuracy, wall-clock time,
hardware utilization, and verified discovery yield remain executable or
empirical obligations.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace RealTimeContinualSchedule

/-- Positive integer work units for one model update and one stream interval.
The ratio `methodWork / streamWork` is the source's relative complexity. -/
structure StreamWorkRatio where
  methodWork : ℕ
  streamWork : ℕ
  methodWork_pos : 0 < methodWork
  streamWork_pos : 0 < streamWork
  deriving DecidableEq, Repr

/-- Raw totalized quotient, exposed so that the zero-cost boundary is not
hidden by the well-formed profile. -/
def rawCompletedUpdates
    (methodWork streamWork steps : ℕ) : ℕ :=
  steps * streamWork / methodWork

/-- Work made available by the stream during the declared horizon. -/
def availableWork (ratio : StreamWorkRatio) (steps : ℕ) : ℕ :=
  steps * ratio.streamWork

/-- Greatest number of whole method updates affordable by that work. -/
def completedUpdates (ratio : StreamWorkRatio) (steps : ℕ) : ℕ :=
  rawCompletedUpdates ratio.methodWork ratio.streamWork steps

/-- Work consumed by all completed updates. -/
def consumedWork (ratio : StreamWorkRatio) (steps : ℕ) : ℕ :=
  completedUpdates ratio steps * ratio.methodWork

/-- Work accumulated toward the next incomplete update. -/
def residualWork (ratio : StreamWorkRatio) (steps : ℕ) : ℕ :=
  availableWork ratio steps % ratio.methodWork

/-- Stream arrivals not paired with a completed model update. This quantity is
used only when the method is no faster than the stream. -/
def skippedStreamSteps (ratio : StreamWorkRatio) (steps : ℕ) : ℕ :=
  steps - completedUpdates ratio steps

theorem consumedWork_le_availableWork
    (ratio : StreamWorkRatio) (steps : ℕ) :
    consumedWork ratio steps ≤ availableWork ratio steps := by
  exact Nat.div_mul_le_self
    (availableWork ratio steps) ratio.methodWork

theorem completedUpdates_maximal
    (ratio : StreamWorkRatio) (steps candidate : ℕ)
    (candidate_fits :
      candidate * ratio.methodWork ≤ availableWork ratio steps) :
    candidate ≤ completedUpdates ratio steps := by
  exact (Nat.le_div_iff_mul_le ratio.methodWork_pos).2 candidate_fits

theorem consumed_add_residual_eq_available
    (ratio : StreamWorkRatio) (steps : ℕ) :
    ratio.methodWork * completedUpdates ratio steps +
        residualWork ratio steps =
      availableWork ratio steps := by
  exact Nat.div_add_mod (availableWork ratio steps) ratio.methodWork

theorem residualWork_lt_methodWork
    (ratio : StreamWorkRatio) (steps : ℕ) :
    residualWork ratio steps < ratio.methodWork := by
  exact Nat.mod_lt _ ratio.methodWork_pos

/-- A method at least as expensive as the stream interval cannot complete
more updates than there have been stream arrivals. -/
theorem completedUpdates_le_steps
    (ratio : StreamWorkRatio) (steps : ℕ)
    (no_faster : ratio.streamWork ≤ ratio.methodWork) :
    completedUpdates ratio steps ≤ steps := by
  apply Nat.div_le_of_le_mul
  calc
    steps * ratio.streamWork ≤ steps * ratio.methodWork :=
      Nat.mul_le_mul_left steps no_faster
    _ = ratio.methodWork * steps := Nat.mul_comm _ _

theorem completed_add_skipped_eq_steps
    (ratio : StreamWorkRatio) (steps : ℕ)
    (no_faster : ratio.streamWork ≤ ratio.methodWork) :
    completedUpdates ratio steps + skippedStreamSteps ratio steps = steps := by
  unfold skippedStreamSteps
  exact Nat.add_sub_of_le
    (completedUpdates_le_steps ratio steps no_faster)

/-! ## Exact source-table schedules -/

def unitRatio : StreamWorkRatio where
  methodWork := 1
  streamWork := 1
  methodWork_pos := by decide
  streamWork_pos := by decide

def fourThirdsRatio : StreamWorkRatio where
  methodWork := 4
  streamWork := 3
  methodWork_pos := by decide
  streamWork_pos := by decide

def twoRatio : StreamWorkRatio where
  methodWork := 2
  streamWork := 1
  methodWork_pos := by decide
  streamWork_pos := by decide

def fiveHalvesRatio : StreamWorkRatio where
  methodWork := 5
  streamWork := 2
  methodWork_pos := by decide
  streamWork_pos := by decide

def threeRatio : StreamWorkRatio where
  methodWork := 3
  streamWork := 1
  methodWork_pos := by decide
  streamWork_pos := by decide

def sixRatio : StreamWorkRatio where
  methodWork := 6
  streamWork := 1
  methodWork_pos := by decide
  streamWork_pos := by decide

theorem unit_ratio_updates_every_step (steps : ℕ) :
    completedUpdates unitRatio steps = steps := by
  simp [completedUpdates, rawCompletedUpdates, unitRatio]

theorem source_table_sixty_step_schedule :
    completedUpdates unitRatio 60 = 60 ∧
      completedUpdates fourThirdsRatio 60 = 45 ∧
      completedUpdates twoRatio 60 = 30 ∧
      completedUpdates fiveHalvesRatio 60 = 24 ∧
      completedUpdates threeRatio 60 = 20 ∧
      completedUpdates sixRatio 60 = 10 := by
  norm_num [completedUpdates, rawCompletedUpdates, unitRatio,
    fourThirdsRatio, twoRatio, fiveHalvesRatio, threeRatio, sixRatio]

theorem source_table_sixty_step_skips :
    skippedStreamSteps unitRatio 60 = 0 ∧
      skippedStreamSteps fourThirdsRatio 60 = 15 ∧
      skippedStreamSteps twoRatio 60 = 30 ∧
      skippedStreamSteps fiveHalvesRatio 60 = 36 ∧
      skippedStreamSteps threeRatio 60 = 40 ∧
      skippedStreamSteps sixRatio 60 = 50 := by
  norm_num [skippedStreamSteps, completedUpdates, rawCompletedUpdates,
    unitRatio, fourThirdsRatio, twoRatio, fiveHalvesRatio, threeRatio,
    sixRatio]

/-- Integer-rounding the source's `4/3` complexity down to one destroys the
work-rate comparison. -/
theorem rounding_four_thirds_to_one_overallocates :
    completedUpdates unitRatio 60 = 60 ∧
      completedUpdates fourThirdsRatio 60 = 45 ∧
      completedUpdates fourThirdsRatio 60 <
        completedUpdates unitRatio 60 := by
  norm_num [completedUpdates, rawCompletedUpdates, unitRatio,
    fourThirdsRatio]

/-- Natural-number division is totalized at zero. The result is not a
meaningful zero-cost schedule, so `StreamWorkRatio` requires positive method
work. -/
theorem zero_method_work_totalization_erases_updates :
    rawCompletedUpdates 0 1 60 = 0 := by
  norm_num [rawCompletedUpdates]

#print axioms consumedWork_le_availableWork
#print axioms completedUpdates_maximal
#print axioms consumed_add_residual_eq_available
#print axioms residualWork_lt_methodWork
#print axioms completedUpdates_le_steps
#print axioms source_table_sixty_step_schedule
#print axioms rounding_four_thirds_to_one_overallocates
#print axioms zero_method_work_totalization_erases_updates

end RealTimeContinualSchedule

end Mettapedia.MachineLearning.ContinualLearning
