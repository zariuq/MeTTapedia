import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Langevin predictive coding: scalar Gaussian moment boundaries

Langevin predictive coding adds Gaussian noise to the usual latent-state
inference step and interprets the resulting trajectory as an unadjusted
Langevin chain.  This file isolates the exactly solvable scalar Gaussian case.
It proves the algebraic equivalence between a predictive-coding score step and
Euler--Maruyama, then follows the mean and variance of the affine noisy update.

The finite-step conclusions are sharper than the informal continuous-time
intuition:

* the effective step must lie strictly between zero and two;
* Euler noise has an exactly computable stationary-variance bias;
* decreasing the step removes that bias only in a limit;
* a corrected discrete noise variance preserves the target variance exactly;
* at and beyond the stability boundary, positive injected noise cannot have a
  finite stationary variance.

Primary correspondence:

* U. Zahid, Q. Guo, and Z. Fountas, *Sample as you Infer: Predictive Coding
  with Langevin Dynamics*, ICML 2024, PMLR 235, Equations (1), (3)--(5), and
  (18)--(20).

The source discusses general nonlinear posterior sampling.  The theorems below
cover a scalar Gaussian target and its exact first two moments under an
independent centered unit-variance noise packet.  They do not claim
distributional convergence for nonlinear chains or validate omission of the
state-dependent metric-divergence term.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LangevinPredictiveCodingMoments

/-- Scalar Gaussian target in precision coordinates. -/
structure ScalarGaussianTarget where
  center : ℝ
  precision : ℝ

/-- Negative log-density up to an additive constant. -/
noncomputable def scalarGaussianPotential
    (target : ScalarGaussianTarget) (state : ℝ) : ℝ :=
  (target.precision / 2) * (state - target.center) ^ 2

/-- Score of the scalar Gaussian target. -/
def scalarGaussianScore
    (target : ScalarGaussianTarget) (state : ℝ) : ℝ :=
  -target.precision * (state - target.center)

/-- The declared score is the negative derivative of the potential. -/
theorem scalarGaussianPotential_hasDerivAt
    (target : ScalarGaussianTarget) (state : ℝ) :
    HasDerivAt (scalarGaussianPotential target)
      (target.precision * (state - target.center)) state := by
  unfold scalarGaussianPotential
  have derivative :
      HasDerivAt
        (fun value : ℝ =>
          (target.precision / 2) * (value - target.center) ^ 2)
        ((target.precision / 2) * (2 * (state - target.center))) state := by
    simpa [Function.id_def] using
      (((hasDerivAt_id state).sub_const target.center).pow 2).const_mul
        (target.precision / 2)
  convert derivative using 1
  ring

theorem scalarGaussianScore_eq_neg_derivative
    (target : ScalarGaussianTarget) (state : ℝ) :
    scalarGaussianScore target state =
      -deriv (scalarGaussianPotential target) state := by
  rw [(scalarGaussianPotential_hasDerivAt target state).deriv]
  simp [scalarGaussianScore]

/-- Deterministic predictive-coding inference step on the Gaussian energy. -/
def scalarPCInferenceStep
    (target : ScalarGaussianTarget) (rate state : ℝ) : ℝ :=
  state + rate * scalarGaussianScore target state

/-- Predictive-coding step with a declared additive noise packet. -/
noncomputable def scalarLangevinPCStep
    (target : ScalarGaussianTarget) (rate noise state : ℝ) : ℝ :=
  scalarPCInferenceStep target rate state +
    Real.sqrt (2 * rate) * noise

/-- Closed Euler--Maruyama update for the same Gaussian score. -/
noncomputable def scalarEulerMaruyamaStep
    (target : ScalarGaussianTarget) (rate noise state : ℝ) : ℝ :=
  state - rate * target.precision * (state - target.center) +
    Real.sqrt (2 * rate) * noise

/-- Injecting the source's scaled noise into the PC score step is exactly the
Euler--Maruyama expression, not merely an analogy. -/
theorem scalarLangevinPCStep_eq_eulerMaruyama
    (target : ScalarGaussianTarget) (rate noise state : ℝ) :
    scalarLangevinPCStep target rate noise state =
      scalarEulerMaruyamaStep target rate noise state := by
  simp [scalarLangevinPCStep, scalarPCInferenceStep,
    scalarEulerMaruyamaStep, scalarGaussianScore]
  ring

/-- For nonnegative rate, the source's noise scale has variance factor
`2 * rate` under unit-variance noise. -/
theorem sourceNoiseScale_sq
    (rate : ℝ) (rate_nonnegative : 0 ≤ rate) :
    (Real.sqrt (2 * rate)) ^ 2 = 2 * rate := by
  exact Real.sq_sqrt (mul_nonneg (by norm_num) rate_nonnegative)

/-! ## Exact moment dynamics -/

/-- First two centered moments of an affine noisy state. -/
@[ext] structure ScalarMomentState where
  meanError : ℝ
  variance : ℝ

/-- Mean/variance transport for
`error' = drift * error + centeredNoise`, assuming the noise packet is
independent and has the declared variance. -/
def scalarAffineNoiseMomentStep
    (drift noiseVariance : ℝ) (state : ScalarMomentState) :
    ScalarMomentState where
  meanError := drift * state.meanError
  variance := drift ^ 2 * state.variance + noiseVariance

/-- Effective scalar drift of a diagonally preconditioned Langevin step. -/
def preconditionedLangevinDrift
    (precision rate metric : ℝ) : ℝ :=
  1 - rate * metric * precision

/-- Moment step induced by the source's preconditioned Euler noise rule. -/
def preconditionedLangevinMomentStep
    (precision rate metric : ℝ) (state : ScalarMomentState) :
    ScalarMomentState :=
  scalarAffineNoiseMomentStep
    (preconditionedLangevinDrift precision rate metric)
    (2 * rate * metric) state

/-- A finite moment trace. -/
def runPreconditionedLangevinMoments
    (precision rate metric : ℝ) :
    ℕ → ScalarMomentState → ScalarMomentState
  | 0, state => state
  | steps + 1, state =>
      preconditionedLangevinMomentStep precision rate metric
        (runPreconditionedLangevinMoments precision rate metric steps state)

/-- The exact stability interval is a condition on the product of rate,
preconditioner, and precision. -/
theorem abs_preconditionedLangevinDrift_lt_one_iff
    (precision rate metric : ℝ) :
    |preconditionedLangevinDrift precision rate metric| < 1 ↔
      0 < rate * metric * precision ∧
        rate * metric * precision < 2 := by
  rw [abs_lt]
  unfold preconditionedLangevinDrift
  constructor <;> rintro ⟨lower, upper⟩ <;> constructor <;> nlinarith

/-- Stationary variance of the scalar Euler moment recursion, when its
denominators are valid. -/
noncomputable def eulerStationaryVariance
    (precision rate metric : ℝ) : ℝ :=
  2 / (precision * (2 - rate * metric * precision))

/-- The closed form is genuinely a fixed variance of the finite Euler moment
step. -/
theorem eulerStationaryVariance_fixed
    (precision rate metric : ℝ)
    (precision_ne : precision ≠ 0)
    (stability_denominator_ne : 2 - rate * metric * precision ≠ 0) :
    (preconditionedLangevinMomentStep precision rate metric
      { meanError := 0
        variance := eulerStationaryVariance precision rate metric }).variance =
      eulerStationaryVariance precision rate metric := by
  unfold preconditionedLangevinMomentStep scalarAffineNoiseMomentStep
    preconditionedLangevinDrift eulerStationaryVariance
  field_simp [precision_ne, stability_denominator_ne]
  ring

/-- Exact one-step transport of variance error around the Euler stationary
variance. -/
theorem variance_error_step_exact
    (precision rate metric : ℝ) (state : ScalarMomentState)
    (precision_ne : precision ≠ 0)
    (stability_denominator_ne : 2 - rate * metric * precision ≠ 0) :
    (preconditionedLangevinMomentStep precision rate metric state).variance -
        eulerStationaryVariance precision rate metric =
      preconditionedLangevinDrift precision rate metric ^ 2 *
        (state.variance - eulerStationaryVariance precision rate metric) := by
  unfold preconditionedLangevinMomentStep scalarAffineNoiseMomentStep
    preconditionedLangevinDrift eulerStationaryVariance
  field_simp [precision_ne, stability_denominator_ne]
  ring

/-- Exact finite-horizon variance error around the Euler stationary value. -/
theorem run_variance_error_exact
    (precision rate metric : ℝ) (steps : ℕ) (initial : ScalarMomentState)
    (precision_ne : precision ≠ 0)
    (stability_denominator_ne : 2 - rate * metric * precision ≠ 0) :
    (runPreconditionedLangevinMoments precision rate metric steps initial).variance -
        eulerStationaryVariance precision rate metric =
      (preconditionedLangevinDrift precision rate metric ^ 2) ^ steps *
        (initial.variance -
          eulerStationaryVariance precision rate metric) := by
  induction steps with
  | zero =>
      simp [runPreconditionedLangevinMoments]
  | succ steps induction_hypothesis =>
      rw [runPreconditionedLangevinMoments]
      rw [variance_error_step_exact precision rate metric
        (runPreconditionedLangevinMoments precision rate metric steps initial)
        precision_ne stability_denominator_ne]
      rw [induction_hypothesis]
      ring

/-! ## Finite-step bias and an exact discrete correction -/

/-- Exact stationary-variance bias of Euler discretization relative to the
target Gaussian variance `1 / precision`. -/
theorem eulerStationaryVariance_sub_target_exact
    (precision rate metric : ℝ)
    (precision_ne : precision ≠ 0)
    (stability_denominator_ne : 2 - rate * metric * precision ≠ 0) :
    eulerStationaryVariance precision rate metric - 1 / precision =
      rate * metric / (2 - rate * metric * precision) := by
  have reordered_denominator_ne :
      2 - precision * rate * metric ≠ 0 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      stability_denominator_ne
  unfold eulerStationaryVariance
  field_simp [precision_ne, stability_denominator_ne,
    reordered_denominator_ne]
  ring

/-- Inside the positive stability interval, the Euler stationary variance is
strictly larger than the intended Gaussian variance. -/
theorem targetVariance_lt_eulerStationaryVariance
    (precision rate metric : ℝ)
    (precision_pos : 0 < precision) (rate_pos : 0 < rate)
    (metric_pos : 0 < metric)
    (effective_step_lt_two : rate * metric * precision < 2) :
    1 / precision <
      eulerStationaryVariance precision rate metric := by
  rw [← sub_pos]
  rw [eulerStationaryVariance_sub_target_exact precision rate metric
    (ne_of_gt precision_pos) (by nlinarith)]
  positivity

/-- Noise variance that makes the target variance exactly invariant under the
finite affine drift. -/
def exactDiscreteNoiseVariance
    (precision rate metric : ℝ) : ℝ :=
  2 * rate * metric - (rate * metric) ^ 2 * precision

/-- Moment step using the exact discrete Gaussian noise variance. -/
def exactDiscreteGaussianMomentStep
    (precision rate metric : ℝ) (state : ScalarMomentState) :
    ScalarMomentState :=
  scalarAffineNoiseMomentStep
    (preconditionedLangevinDrift precision rate metric)
    (exactDiscreteNoiseVariance precision rate metric) state

/-- The corrected finite step preserves the intended target variance exactly. -/
theorem exactDiscreteNoise_preserves_targetVariance
    (precision rate metric : ℝ) (precision_ne : precision ≠ 0) :
    exactDiscreteGaussianMomentStep precision rate metric
      { meanError := 0, variance := 1 / precision } =
        { meanError := 0, variance := 1 / precision } := by
  ext <;>
    simp [exactDiscreteGaussianMomentStep, scalarAffineNoiseMomentStep,
      preconditionedLangevinDrift, exactDiscreteNoiseVariance]
  field_simp [precision_ne]
  ring

/-- Euler injects an additional positive second-order variance term beyond the
exact discrete invariant-noise rule. -/
theorem eulerNoise_sub_exactDiscreteNoise
    (precision rate metric : ℝ) :
    2 * rate * metric - exactDiscreteNoiseVariance precision rate metric =
      (rate * metric) ^ 2 * precision := by
  simp [exactDiscreteNoiseVariance]

theorem exactDiscreteNoiseVariance_pos_of_stable
    (precision rate metric : ℝ)
    (_precision_pos : 0 < precision) (rate_pos : 0 < rate)
    (metric_pos : 0 < metric)
    (effective_step_lt_two : rate * metric * precision < 2) :
    0 < exactDiscreteNoiseVariance precision rate metric := by
  unfold exactDiscreteNoiseVariance
  nlinarith [mul_pos rate_pos metric_pos]

/-! ## Critical and unstable boundaries -/

/-- At effective step two the deterministic mean flips sign while the
variance gains the full positive noise injection on every step. -/
theorem critical_effectiveStep_two
    (precision rate metric : ℝ)
    (critical : rate * metric * precision = 2)
    (state : ScalarMomentState) :
    preconditionedLangevinMomentStep precision rate metric state =
      { meanError := -state.meanError
        variance := state.variance + 2 * rate * metric } := by
  ext <;>
    simp [preconditionedLangevinMomentStep, scalarAffineNoiseMomentStep,
      preconditionedLangevinDrift, critical] <;>
    ring

/-- Positive noise at the critical step precludes any finite fixed variance. -/
theorem critical_effectiveStep_has_no_fixed_variance
    (precision rate metric variance : ℝ)
    (rate_pos : 0 < rate) (metric_pos : 0 < metric)
    (critical : rate * metric * precision = 2) :
    (preconditionedLangevinMomentStep precision rate metric
      { meanError := 0, variance := variance }).variance ≠ variance := by
  rw [show
    (preconditionedLangevinMomentStep precision rate metric
      { meanError := 0, variance := variance }).variance =
        variance + 2 * rate * metric by
      rw [critical_effectiveStep_two precision rate metric critical]]
  nlinarith [mul_pos rate_pos metric_pos]

/-- An executable beyond-boundary fixture: the variance grows from one to ten
in a single step. -/
theorem oversized_step :
    preconditionedLangevinMomentStep 1 3 1
      { meanError := 1, variance := 1 } =
        { meanError := -2, variance := 10 } := by
  norm_num [preconditionedLangevinMomentStep,
    scalarAffineNoiseMomentStep, preconditionedLangevinDrift]

/-- A unit effective step forgets the initial mean in one move, but Euler noise
still doubles the target variance. -/
theorem unit_effectiveStep :
    preconditionedLangevinMomentStep 1 1 1
      { meanError := 7, variance := 1 } =
        { meanError := 0, variance := 2 } := by
  norm_num [preconditionedLangevinMomentStep,
    scalarAffineNoiseMomentStep, preconditionedLangevinDrift]

#print axioms scalarGaussianPotential_hasDerivAt
#print axioms scalarLangevinPCStep_eq_eulerMaruyama
#print axioms sourceNoiseScale_sq
#print axioms abs_preconditionedLangevinDrift_lt_one_iff
#print axioms eulerStationaryVariance_fixed
#print axioms variance_error_step_exact
#print axioms run_variance_error_exact
#print axioms eulerStationaryVariance_sub_target_exact
#print axioms targetVariance_lt_eulerStationaryVariance
#print axioms exactDiscreteNoise_preserves_targetVariance
#print axioms exactDiscreteNoiseVariance_pos_of_stable
#print axioms critical_effectiveStep_has_no_fixed_variance
#print axioms oversized_step

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LangevinPredictiveCodingMoments
