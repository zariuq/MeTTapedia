import Mathlib

/-!
# Cyclical learning-rate geometry on quadratic modes

Smith, *Cyclical Learning Rates for Training Neural Networks*
(arXiv:1506.01186), proposes periodically varying the global learning rate and
emphasizes that increasing the rate can hurt performance temporarily while
helping over a complete cycle.  Smith and Topin, *Super-Convergence: Very Fast
Training of Neural Networks Using Large Learning Rates*
(arXiv:1708.07120), sharpen this into a one-cycle policy with a large maximum
rate.

This file isolates the exact finite algebra visible on one scalar quadratic
mode.  An arbitrary finite rate schedule acts by the product of its per-step
multipliers.  Repeating a cycle raises that gain to a power, and squared loss
scales by the square of the gain.  A concrete two-step cycle first quadruples
the loss with a rate outside the single-step stability interval, then contracts
enough to beat two matched-work small-rate steps.  A nearby cycle instead
expands, so a large maximum rate is not itself a stability certificate.

The scalar fixed-curvature model is deliberately limited: its gain is
invariant under schedule reversal.  Any advantage depending on the order of
the rising and falling portions must therefore use curvature variation,
noncommuting modes, stochasticity, momentum, regularization, or another
mechanism absent here.  No empirical speed, accuracy, or generalization claim
is formalized.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CyclicalLearningRateGeometry

noncomputable section

/-- Half-squared loss on a scalar mode with declared curvature. -/
def scalarQuadraticLoss (curvature state : ℝ) : ℝ :=
  curvature * state ^ 2 / 2

/-- One gradient step on `curvature * state^2 / 2`. -/
def scalarQuadraticStep
    (curvature learningRate state : ℝ) : ℝ :=
  state - learningRate * curvature * state

/-- Execute learning rates in list order. -/
def runRateSchedule (curvature : ℝ) :
    List ℝ → ℝ → ℝ
  | [], state => state
  | learningRate :: schedule, state =>
      runRateSchedule curvature schedule
        (scalarQuadraticStep curvature learningRate state)

/-- Terminal multiplier of a finite scalar quadratic schedule. -/
def scheduleGain (curvature : ℝ) : List ℝ → ℝ
  | [] => 1
  | learningRate :: schedule =>
      scheduleGain curvature schedule *
        (1 - learningRate * curvature)

/-- Every finite schedule acts by its exact product multiplier. -/
theorem runRateSchedule_eq_scheduleGain_mul
    (curvature : ℝ) (schedule : List ℝ) (state : ℝ) :
    runRateSchedule curvature schedule state =
      scheduleGain curvature schedule * state := by
  induction schedule generalizing state with
  | nil =>
      simp [runRateSchedule, scheduleGain]
  | cons learningRate schedule inductionHypothesis =>
      rw [runRateSchedule, inductionHypothesis]
      simp only [scalarQuadraticStep, scheduleGain]
      ring

/-- Concatenating schedules multiplies their gains. -/
theorem scheduleGain_append
    (curvature : ℝ) (first second : List ℝ) :
    scheduleGain curvature (first ++ second) =
      scheduleGain curvature second *
        scheduleGain curvature first := by
  induction first with
  | nil =>
      simp [scheduleGain]
  | cons learningRate first inductionHypothesis =>
      simp only [List.cons_append, scheduleGain, inductionHypothesis]
      ring

/-- On a fixed scalar quadratic mode, reversing the rate order cannot change
the terminal gain. -/
theorem scheduleGain_reverse
    (curvature : ℝ) (schedule : List ℝ) :
    scheduleGain curvature schedule.reverse =
      scheduleGain curvature schedule := by
  induction schedule with
  | nil =>
      simp [scheduleGain]
  | cons learningRate schedule inductionHypothesis =>
      rw [List.reverse_cons, scheduleGain_append, inductionHypothesis]
      simp [scheduleGain]
      ring

/-- A finite schedule scales half-squared quadratic loss by gain squared. -/
theorem scalarQuadraticLoss_runRateSchedule
    (curvature : ℝ) (schedule : List ℝ) (state : ℝ) :
    scalarQuadraticLoss curvature
        (runRateSchedule curvature schedule state) =
      scheduleGain curvature schedule ^ 2 *
        scalarQuadraticLoss curvature state := by
  rw [runRateSchedule_eq_scheduleGain_mul]
  simp only [scalarQuadraticLoss]
  ring

/-- Repeat one complete finite rate cycle. -/
def runRateCycles
    (curvature : ℝ) (schedule : List ℝ) :
    ℕ → ℝ → ℝ
  | 0, state => state
  | cycles + 1, state =>
      runRateCycles curvature schedule cycles
        (runRateSchedule curvature schedule state)

/-- Repeating a cycle raises its exact gain to the cycle count. -/
theorem runRateCycles_eq_scheduleGain_pow_mul
    (curvature : ℝ) (schedule : List ℝ)
    (cycles : ℕ) (state : ℝ) :
    runRateCycles curvature schedule cycles state =
      scheduleGain curvature schedule ^ cycles * state := by
  induction cycles generalizing state with
  | zero =>
      simp [runRateCycles]
  | succ cycles inductionHypothesis =>
      rw [runRateCycles, inductionHypothesis,
        runRateSchedule_eq_scheduleGain_mul]
      rw [pow_succ]
      ring

/-- Repeated-cycle loss has the corresponding exact geometric law. -/
theorem scalarQuadraticLoss_runRateCycles
    (curvature : ℝ) (schedule : List ℝ)
    (cycles : ℕ) (state : ℝ) :
    scalarQuadraticLoss curvature
        (runRateCycles curvature schedule cycles state) =
      scheduleGain curvature schedule ^ (2 * cycles) *
        scalarQuadraticLoss curvature state := by
  rw [runRateCycles_eq_scheduleGain_pow_mul]
  simp only [scalarQuadraticLoss]
  ring

/-- A cycle with gain strictly inside the unit disk converges to the quadratic
fixed point from every scalar state. -/
theorem runRateCycles_tendsto_zero
    (curvature : ℝ) (schedule : List ℝ) (state : ℝ)
    (contractive : |scheduleGain curvature schedule| < 1) :
    Filter.Tendsto
        (fun cycles =>
          runRateCycles curvature schedule cycles state)
        Filter.atTop (nhds 0) := by
  simpa only [runRateCycles_eq_scheduleGain_pow_mul, zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one contractive).mul_const state

/-! ## Exact finite witnesses -/

def largeThenCorrectiveCycle : List ℝ :=
  [3, 3 / 4]

def twoQuarterRateSteps : List ℝ :=
  [1 / 4, 1 / 4]

def unstableLargeCycle : List ℝ :=
  [3, 1 / 4]

/-- The first large step is outside the single-step stability interval and
quadruples the unit-curvature loss. -/
theorem largeRate_oneStep_quadruples_loss :
    scalarQuadraticLoss 1 (scalarQuadraticStep 1 3 1) =
      4 * scalarQuadraticLoss 1 1 := by
  norm_num [scalarQuadraticLoss, scalarQuadraticStep]

/-- The complete large-then-corrective cycle has gain `-1/2`. -/
theorem largeThenCorrectiveCycle_gain :
    scheduleGain 1 largeThenCorrectiveCycle = -(1 / 2) := by
  norm_num [scheduleGain, largeThenCorrectiveCycle]

/-- Despite its harmful first step, the complete cycle quarters the initial
loss. -/
theorem largeThenCorrectiveCycle_quarters_loss :
    scalarQuadraticLoss 1
        (runRateSchedule 1 largeThenCorrectiveCycle 1) =
      (1 / 4) * scalarQuadraticLoss 1 1 := by
  norm_num [scalarQuadraticLoss, runRateSchedule, scalarQuadraticStep,
    largeThenCorrectiveCycle]

/-- At equal two-step work, the large-then-corrective cycle decreases this
quadratic loss more than two rate-`1/4` steps. -/
theorem largeThenCorrectiveCycle_beats_twoQuarterRateSteps :
    scalarQuadraticLoss 1
        (runRateSchedule 1 largeThenCorrectiveCycle 1) <
      scalarQuadraticLoss 1
        (runRateSchedule 1 twoQuarterRateSteps 1) := by
  norm_num [scalarQuadraticLoss, runRateSchedule, scalarQuadraticStep,
    largeThenCorrectiveCycle, twoQuarterRateSteps]

/-- A nearby cycle containing the same harmful large step has gain `-3/2`
and increases loss, so a large maximum rate alone licenses nothing. -/
theorem unstableLargeCycle_increases_loss :
    scheduleGain 1 unstableLargeCycle = -(3 / 2) ∧
      scalarQuadraticLoss 1
          (runRateSchedule 1 unstableLargeCycle 1) >
        scalarQuadraticLoss 1 1 := by
  norm_num [scheduleGain, scalarQuadraticLoss, runRateSchedule,
    scalarQuadraticStep, unstableLargeCycle]

#print axioms runRateSchedule_eq_scheduleGain_mul
#print axioms scheduleGain_append
#print axioms scheduleGain_reverse
#print axioms scalarQuadraticLoss_runRateSchedule
#print axioms runRateCycles_eq_scheduleGain_pow_mul
#print axioms scalarQuadraticLoss_runRateCycles
#print axioms runRateCycles_tendsto_zero
#print axioms largeRate_oneStep_quadruples_loss
#print axioms largeThenCorrectiveCycle_beats_twoQuarterRateSteps
#print axioms unstableLargeCycle_increases_loss

end

end CyclicalLearningRateGeometry

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
