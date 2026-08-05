import Mathlib.Tactic

/-!
# Bayesian gradient descent: antithetic curvature and uncertainty

Zeno, Golan, Hoffer, and Soudry, *Task Agnostic Continual Learning Using
Online Variational Bayes* (2018, arXiv:1803.10123), equations (11)--(13) and
Theorem 1, derive a diagonal-Gaussian mean update and a closed standard-
deviation update.  Their strong-convexity argument identifies
`E[gradient (mean + deviation * noise) * noise]` as a positive curvature
signal.

This file isolates an executable finite-sample version of that mechanism.
Strong monotonicity of a scalar gradient gives a pointwise lower bound for
each antithetic noise pair.  The bound sums over any finite sample family and,
when its empirical second moment is one, recovers the source theorem's
`modulus * deviation` lower bound without a stochastic approximation inside
the proof.

The source standard-deviation recursion is then proved positive and is shown
to decrease, remain fixed, or increase according to the sign of the curvature
signal.  A one-sided counterexample shows why an unpaired finite sample does
not inherit the expectation-level sign guarantee.

No theorem here identifies a finite antithetic average with an exact Gaussian
expectation, proves convergence of the nonlinear training loop, or validates
the paper's neural-network experiments.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace BayesianGradientDescent

/-- A scalar gradient is strongly monotone with modulus `modulus` when its
secants dominate the corresponding quadratic displacement. -/
def StronglyMonotoneGradient
    (modulus : ℝ) (gradient : ℝ → ℝ) : Prop :=
  ∀ first second,
    modulus * (first - second) ^ 2 ≤
      (gradient first - gradient second) * (first - second)

/-- Curvature signal from a symmetric pair `noise` and `-noise`. -/
noncomputable def pairedCurvatureSignal
    (gradient : ℝ → ℝ)
    (center deviation noise : ℝ) : ℝ :=
  (gradient (center + deviation * noise) * noise +
      gradient (center - deviation * noise) * (-noise)) / 2

/-- A single unpaired sample, included to state the sampling boundary. -/
noncomputable def oneSidedCurvatureSignal
    (gradient : ℝ → ℝ)
    (center deviation noise : ℝ) : ℝ :=
  gradient (center + deviation * noise) * noise

/-- Each antithetic pair inherits the strong-monotonicity curvature bound. -/
theorem modulus_mul_deviation_mul_noiseSq_le_pairedCurvatureSignal
    {modulus center deviation noise : ℝ}
    {gradient : ℝ → ℝ}
    (strong : StronglyMonotoneGradient modulus gradient)
    (deviation_positive : 0 < deviation) :
    modulus * deviation * noise ^ 2 ≤
      pairedCurvatureSignal gradient center deviation noise := by
  have secant :=
    strong (center + deviation * noise) (center - deviation * noise)
  unfold pairedCurvatureSignal
  nlinarith

/-- Sum of antithetic curvature signals over a finite sample family. -/
noncomputable def totalPairedCurvature
    {Sample : Type*} [Fintype Sample]
    (gradient : ℝ → ℝ)
    (center deviation : ℝ)
    (noise : Sample → ℝ) : ℝ :=
  ∑ sample, pairedCurvatureSignal gradient center deviation (noise sample)

/-- Empirical second-moment mass of the same finite sample family. -/
noncomputable def totalNoiseSquare
    {Sample : Type*} [Fintype Sample]
    (noise : Sample → ℝ) : ℝ :=
  ∑ sample, noise sample ^ 2

/-- The pointwise antithetic certificate composes over an arbitrary finite
sample family. -/
theorem modulus_mul_deviation_mul_totalNoiseSquare_le_totalPairedCurvature
    {Sample : Type*} [Fintype Sample]
    {modulus center deviation : ℝ}
    {gradient : ℝ → ℝ}
    (noise : Sample → ℝ)
    (strong : StronglyMonotoneGradient modulus gradient)
    (deviation_positive : 0 < deviation) :
    modulus * deviation * totalNoiseSquare noise ≤
      totalPairedCurvature gradient center deviation noise := by
  unfold totalNoiseSquare totalPairedCurvature
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun sample _ =>
    modulus_mul_deviation_mul_noiseSq_le_pairedCurvatureSignal
      strong deviation_positive

/-- Finite antithetic average of the curvature signal. -/
noncomputable def averagePairedCurvature
    {Sample : Type*} [Fintype Sample]
    (gradient : ℝ → ℝ)
    (center deviation : ℝ)
    (noise : Sample → ℝ) : ℝ :=
  totalPairedCurvature gradient center deviation noise / Fintype.card Sample

/-- Unit empirical second moment recovers the source-shaped lower bound
`modulus * deviation` for a finite antithetic average. -/
theorem modulus_mul_deviation_le_averagePairedCurvature
    {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    {modulus center deviation : ℝ}
    {gradient : ℝ → ℝ}
    (noise : Sample → ℝ)
    (strong : StronglyMonotoneGradient modulus gradient)
    (deviation_positive : 0 < deviation)
    (unitSecondMoment :
      totalNoiseSquare noise = Fintype.card Sample) :
    modulus * deviation ≤
      averagePairedCurvature gradient center deviation noise := by
  have totalBound :=
    modulus_mul_deviation_mul_totalNoiseSquare_le_totalPairedCurvature
      (center := center) noise strong deviation_positive
  have card_positive : (0 : ℝ) < Fintype.card Sample := by
    exact_mod_cast Fintype.card_pos
  unfold averagePairedCurvature
  rw [unitSecondMoment] at totalBound
  apply (le_div_iff₀ card_positive).2
  nlinarith

/-- Linear gradient of a scalar quadratic loss. -/
def quadraticGradient (curvature : ℝ) : ℝ → ℝ :=
  fun parameter => curvature * parameter

theorem quadraticGradient_stronglyMonotone
    {curvature : ℝ} :
    StronglyMonotoneGradient curvature (quadraticGradient curvature) := by
  intro first second
  unfold quadraticGradient
  ring_nf
  exact le_rfl

/-- For a quadratic, the antithetic certificate is exact pair by pair. -/
theorem quadratic_pairedCurvatureSignal_exact
    (curvature center deviation noise : ℝ) :
    pairedCurvatureSignal (quadraticGradient curvature)
        center deviation noise =
      curvature * deviation * noise ^ 2 := by
  unfold pairedCurvatureSignal quadraticGradient
  ring

/-- Positive fixture: unit antithetic noise exactly recovers the curvature
times the deviation. -/
theorem unitNoise_quadratic :
    pairedCurvatureSignal (quadraticGradient 2) 7 3 1 = 6 := by
  norm_num [quadratic_pairedCurvatureSignal_exact]

/-- Negative fixture: a one-sided finite sample can report a negative signal
even for the unit strongly convex quadratic. -/
theorem oneSided_sample_can_reverse_positive_curvature :
    StronglyMonotoneGradient 1 (quadraticGradient 1) ∧
      oneSidedCurvatureSignal (quadraticGradient 1) (-2) 1 1 = -1 := by
  constructor
  · exact quadraticGradient_stronglyMonotone
  · norm_num [oneSidedCurvatureSignal, quadraticGradient]

/-! ## Source standard-deviation recursion -/

/-- Equation (12), with `curvatureSignal` standing for
`E[gradient * noise]`. -/
noncomputable def uncertaintyUpdate
    (priorDeviation curvatureSignal : ℝ) : ℝ :=
  priorDeviation *
    (Real.sqrt (1 + (priorDeviation * curvatureSignal / 2) ^ 2) -
      priorDeviation * curvatureSignal / 2)

private theorem sqrt_one_add_sq_sub_pos (value : ℝ) :
    0 < Real.sqrt (1 + value ^ 2) - value := by
  have radicand_nonnegative : 0 ≤ 1 + value ^ 2 := by positivity
  have sqrt_nonnegative : 0 ≤ Real.sqrt (1 + value ^ 2) :=
    Real.sqrt_nonneg _
  have sqrt_square :
      (Real.sqrt (1 + value ^ 2)) ^ 2 = 1 + value ^ 2 :=
    Real.sq_sqrt radicand_nonnegative
  by_cases value_negative : value < 0
  · nlinarith
  · have value_nonnegative : 0 ≤ value := le_of_not_gt value_negative
    nlinarith

private theorem sqrt_one_add_sq_lt_one_add
    {value : ℝ} (value_positive : 0 < value) :
    Real.sqrt (1 + value ^ 2) < 1 + value := by
  have radicand_nonnegative : 0 ≤ 1 + value ^ 2 := by positivity
  have sqrt_nonnegative : 0 ≤ Real.sqrt (1 + value ^ 2) :=
    Real.sqrt_nonneg _
  have sqrt_square :
      (Real.sqrt (1 + value ^ 2)) ^ 2 = 1 + value ^ 2 :=
    Real.sq_sqrt radicand_nonnegative
  nlinarith

private theorem one_lt_sqrt_one_add_sq_sub
    {value : ℝ} (value_negative : value < 0) :
    1 < Real.sqrt (1 + value ^ 2) - value := by
  have radicand_nonnegative : 0 ≤ 1 + value ^ 2 := by positivity
  have sqrt_nonnegative : 0 ≤ Real.sqrt (1 + value ^ 2) :=
    Real.sqrt_nonneg _
  have sqrt_square :
      (Real.sqrt (1 + value ^ 2)) ^ 2 = 1 + value ^ 2 :=
    Real.sq_sqrt radicand_nonnegative
  have one_le_sqrt : 1 ≤ Real.sqrt (1 + value ^ 2) := by
    nlinarith [sq_nonneg value]
  nlinarith

theorem uncertaintyUpdate_positive
    {priorDeviation curvatureSignal : ℝ}
    (prior_positive : 0 < priorDeviation) :
    0 < uncertaintyUpdate priorDeviation curvatureSignal := by
  unfold uncertaintyUpdate
  exact mul_pos prior_positive
    (sqrt_one_add_sq_sub_pos (priorDeviation * curvatureSignal / 2))

theorem uncertaintyUpdate_zero_signal
    (priorDeviation : ℝ) :
    uncertaintyUpdate priorDeviation 0 = priorDeviation := by
  simp [uncertaintyUpdate]

theorem uncertaintyUpdate_lt_prior_of_positive_signal
    {priorDeviation curvatureSignal : ℝ}
    (prior_positive : 0 < priorDeviation)
    (signal_positive : 0 < curvatureSignal) :
    uncertaintyUpdate priorDeviation curvatureSignal < priorDeviation := by
  have scaled_positive :
      0 < priorDeviation * curvatureSignal / 2 := by positivity
  have root_bound :=
    sqrt_one_add_sq_lt_one_add scaled_positive
  unfold uncertaintyUpdate
  nlinarith

theorem prior_lt_uncertaintyUpdate_of_negative_signal
    {priorDeviation curvatureSignal : ℝ}
    (prior_positive : 0 < priorDeviation)
    (signal_negative : curvatureSignal < 0) :
    priorDeviation < uncertaintyUpdate priorDeviation curvatureSignal := by
  have scaled_negative :
      priorDeviation * curvatureSignal / 2 < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg prior_positive signal_negative)
      (by norm_num)
  have root_bound :=
    one_lt_sqrt_one_add_sq_sub scaled_negative
  unfold uncertaintyUpdate
  nlinarith

/-- A positive strong-curvature certificate makes the BGD uncertainty
strictly decrease. -/
theorem antithetic_strong_curvature_decreases_uncertainty
    {Sample : Type*} [Fintype Sample] [Nonempty Sample]
    {modulus center deviation priorDeviation : ℝ}
    {gradient : ℝ → ℝ}
    (noise : Sample → ℝ)
    (strong : StronglyMonotoneGradient modulus gradient)
    (modulus_positive : 0 < modulus)
    (deviation_positive : 0 < deviation)
    (prior_positive : 0 < priorDeviation)
    (unitSecondMoment :
      totalNoiseSquare noise = Fintype.card Sample) :
    uncertaintyUpdate priorDeviation
        (averagePairedCurvature gradient center deviation noise) <
      priorDeviation := by
  have signal_lower :=
    modulus_mul_deviation_le_averagePairedCurvature
      (center := center) noise strong deviation_positive unitSecondMoment
  have signal_positive :
      0 < averagePairedCurvature gradient center deviation noise := by
    nlinarith
  exact uncertaintyUpdate_lt_prior_of_positive_signal
    prior_positive signal_positive

/-- Negative-curvature fixture: the uncertainty increases. -/
theorem concave_quadratic_increases_uncertainty :
    1 < uncertaintyUpdate 1
      (pairedCurvatureSignal (quadraticGradient (-1)) 0 1 1) := by
  apply prior_lt_uncertaintyUpdate_of_negative_signal
  · norm_num
  · rw [quadratic_pairedCurvatureSignal_exact]
    norm_num

#print axioms modulus_mul_deviation_le_averagePairedCurvature
#print axioms oneSided_sample_can_reverse_positive_curvature
#print axioms uncertaintyUpdate_positive
#print axioms uncertaintyUpdate_lt_prior_of_positive_signal
#print axioms prior_lt_uncertaintyUpdate_of_negative_signal
#print axioms antithetic_strong_curvature_decreases_uncertainty
#print axioms concave_quadratic_increases_uncertainty

end BayesianGradientDescent

end Mettapedia.MachineLearning.ContinualLearning
