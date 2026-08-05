import Mathlib

/-!
# Stochastic semantic-memory updates

Arani, Sarfraz, and Zonooz,
*Learning Fast, Learning Slow: A General Continual Learning Method based on
Complementary Learning System* (ICLR 2022, arXiv:2201.12604), Algorithm 1 and
Equation (2), maintain plastic and stable semantic memories by stochastic
exponential moving averages of a working model.

This file isolates the exact finite-dimensional geometry of that update.
For update probability `rate` and EMA decay `alpha`, the Bernoulli mean is an
interpolation with effective gain

`rate * (1 - alpha)`.

Consequently:

* the expected fixed-target trajectory is a geometric interpolation;
* the source ordering `rateStable ≤ ratePlastic` and
  `alphaPlastic ≤ alphaStable` makes the plastic mean trajectory no slower;
* neither ordering alone is sufficient;
* different probability/decay pairs can have the same mean trajectory while
  retaining different branch variance.

The last boundary is important: mean dynamics identify only the effective
gain, not the two stochastic-update parameters separately.  These theorems do
not claim a pathwise ordering, a moving-target guarantee, or a neural-loss
retention result.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace StochasticSemanticMemory

noncomputable section

variable {State : Type*}

section Update

variable [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Exponential moving-average update toward the current working state. -/
def emaUpdate (alpha : ℝ) (memory target : State) : State :=
  alpha • memory + (1 - alpha) • target

/-- The two outcomes of the source's stochastic semantic-memory update. -/
def branchUpdate
    (updateNow : Bool) (alpha : ℝ) (memory target : State) : State :=
  if updateNow then emaUpdate alpha memory target else memory

/-- The single scalar controlling the mean interpolation. -/
def effectiveGain (rate alpha : ℝ) : ℝ :=
  rate * (1 - alpha)

/-- Explicit Bernoulli expectation of the two update branches. -/
def bernoulliMean
    (rate alpha : ℝ) (memory target : State) : State :=
  (1 - rate) • memory + rate • emaUpdate alpha memory target

@[simp]
theorem branchUpdate_false
    (alpha : ℝ) (memory target : State) :
    branchUpdate false alpha memory target = memory := by
  simp [branchUpdate]

@[simp]
theorem branchUpdate_true
    (alpha : ℝ) (memory target : State) :
    branchUpdate true alpha memory target = emaUpdate alpha memory target := by
  simp [branchUpdate]

/-- An EMA is an interpolation written in displacement coordinates. -/
theorem emaUpdate_eq_interpolation
    (alpha : ℝ) (memory target : State) :
    emaUpdate alpha memory target =
      memory + (1 - alpha) • (target - memory) := by
  unfold emaUpdate
  module

/-- The stochastic update's mean depends on `rate` and `alpha` only through
their effective gain. -/
theorem bernoulliMean_eq_interpolation
    (rate alpha : ℝ) (memory target : State) :
    bernoulliMean rate alpha memory target =
      memory + effectiveGain rate alpha • (target - memory) := by
  unfold bernoulliMean effectiveGain emaUpdate
  module

/-- Exact mean error after one stochastic semantic-memory update. -/
theorem bernoulliMean_sub_target
    (rate alpha : ℝ) (memory target : State) :
    bernoulliMean rate alpha memory target - target =
      (1 - effectiveGain rate alpha) • (memory - target) := by
  rw [bernoulliMean_eq_interpolation]
  module

/-- A semantic memory already equal to the working state remains fixed. -/
@[simp]
theorem bernoulliMean_fixed
    (rate alpha : ℝ) (target : State) :
    bernoulliMean rate alpha target target = target := by
  unfold bernoulliMean emaUpdate
  module

/-- A zero update probability freezes the memory. -/
@[simp]
theorem bernoulliMean_zero_rate
    (alpha : ℝ) (memory target : State) :
    bernoulliMean 0 alpha memory target = memory := by
  simp [bernoulliMean]

/-- Certain updating recovers the ordinary EMA exactly. -/
@[simp]
theorem bernoulliMean_one_rate
    (alpha : ℝ) (memory target : State) :
    bernoulliMean 1 alpha memory target = emaUpdate alpha memory target := by
  simp [bernoulliMean]

/-- Unit decay freezes both stochastic branches. -/
@[simp]
theorem bernoulliMean_one_alpha
    (rate : ℝ) (memory target : State) :
    bernoulliMean rate 1 memory target = memory := by
  rw [bernoulliMean_eq_interpolation]
  simp [effectiveGain]

/-- Iteration of the mean update against a fixed target. -/
def meanIterate
    (rate alpha : ℝ) (target : State) : ℕ → State → State
  | 0, memory => memory
  | steps + 1, memory =>
      bernoulliMean rate alpha
        (meanIterate rate alpha target steps memory) target

@[simp]
theorem meanIterate_zero
    (rate alpha : ℝ) (target memory : State) :
    meanIterate rate alpha target 0 memory = memory := rfl

@[simp]
theorem meanIterate_succ
    (rate alpha : ℝ) (target memory : State) (steps : ℕ) :
    meanIterate rate alpha target (steps + 1) memory =
      bernoulliMean rate alpha
        (meanIterate rate alpha target steps memory) target := rfl

/-- Exact geometric error trajectory for a fixed working-state target. -/
theorem meanIterate_sub_target
    (rate alpha : ℝ) (target memory : State) :
    ∀ steps,
      meanIterate rate alpha target steps memory - target =
        (1 - effectiveGain rate alpha) ^ steps • (memory - target)
  | 0 => by simp
  | steps + 1 => by
      rw [meanIterate_succ, bernoulliMean_sub_target,
        meanIterate_sub_target rate alpha target memory steps, smul_smul]
      congr 1
      rw [pow_succ]
      ring

/-- Exact norm of the mean error. -/
theorem meanIterate_error_norm
    (rate alpha : ℝ) (target memory : State) (steps : ℕ) :
    ‖meanIterate rate alpha target steps memory - target‖ =
      |1 - effectiveGain rate alpha| ^ steps * ‖memory - target‖ := by
  rw [meanIterate_sub_target, norm_smul, Real.norm_eq_abs, abs_pow]

/-- Valid probability and decay parameters give a nonnegative gain. -/
theorem effectiveGain_nonnegative
    (rate alpha : ℝ)
    (rate_nonnegative : 0 ≤ rate)
    (alpha_le_one : alpha ≤ 1) :
    0 ≤ effectiveGain rate alpha := by
  unfold effectiveGain
  exact mul_nonneg rate_nonnegative (sub_nonneg.mpr alpha_le_one)

/-- Valid probability and decay parameters give gain at most one. -/
theorem effectiveGain_le_one
    (rate alpha : ℝ)
    (rate_le_one : rate ≤ 1)
    (alpha_nonnegative : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) :
    effectiveGain rate alpha ≤ 1 := by
  unfold effectiveGain
  have complement_nonnegative : 0 ≤ 1 - alpha := by linarith
  have complement_le_one : 1 - alpha ≤ 1 := by linarith
  exact mul_le_one₀ rate_le_one complement_nonnegative complement_le_one

/-- Valid stochastic-update parameters place the effective gain in the unit
interval. -/
theorem effectiveGain_mem_Icc
    (rate alpha : ℝ)
    (rate_nonnegative : 0 ≤ rate)
    (rate_le_one : rate ≤ 1)
    (alpha_nonnegative : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) :
    effectiveGain rate alpha ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨
    effectiveGain_nonnegative rate alpha rate_nonnegative alpha_le_one,
    effectiveGain_le_one rate alpha rate_le_one
      alpha_nonnegative alpha_le_one⟩

/-- The mean error factor is nonnegative for valid parameters. -/
theorem meanErrorFactor_nonnegative
    (rate alpha : ℝ)
    (rate_nonnegative : 0 ≤ rate)
    (rate_le_one : rate ≤ 1)
    (alpha_nonnegative : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) :
    0 ≤ 1 - effectiveGain rate alpha := by
  have gain_bounds := effectiveGain_mem_Icc
    rate alpha rate_nonnegative rate_le_one alpha_nonnegative alpha_le_one
  have := gain_bounds.2
  linarith

/-- Faster updates and smaller decay jointly give at least as much effective
mean gain. -/
theorem effectiveGain_stable_le_plastic
    (rateStable ratePlastic alphaStable alphaPlastic : ℝ)
    (rate_order : rateStable ≤ ratePlastic)
    (decay_order : alphaPlastic ≤ alphaStable)
    (ratePlastic_nonnegative : 0 ≤ ratePlastic)
    (alphaStable_le_one : alphaStable ≤ 1) :
    effectiveGain rateStable alphaStable ≤
      effectiveGain ratePlastic alphaPlastic := by
  unfold effectiveGain
  exact mul_le_mul rate_order (by linarith)
    (by linarith) ratePlastic_nonnegative

/-- Under the source's joint parameter ordering, the plastic mean trajectory
has no larger fixed-target error than the stable trajectory. -/
theorem plastic_mean_error_le_stable
    (rateStable ratePlastic alphaStable alphaPlastic : ℝ)
    (target memory : State) (steps : ℕ)
    (rateStable_nonnegative : 0 ≤ rateStable)
    (rateStable_le_one : rateStable ≤ 1)
    (ratePlastic_nonnegative : 0 ≤ ratePlastic)
    (ratePlastic_le_one : ratePlastic ≤ 1)
    (alphaStable_nonnegative : 0 ≤ alphaStable)
    (alphaStable_le_one : alphaStable ≤ 1)
    (alphaPlastic_nonnegative : 0 ≤ alphaPlastic)
    (alphaPlastic_le_one : alphaPlastic ≤ 1)
    (rate_order : rateStable ≤ ratePlastic)
    (decay_order : alphaPlastic ≤ alphaStable) :
    ‖meanIterate ratePlastic alphaPlastic target steps memory - target‖ ≤
      ‖meanIterate rateStable alphaStable target steps memory - target‖ := by
  rw [meanIterate_error_norm, meanIterate_error_norm]
  have gain_order :
      effectiveGain rateStable alphaStable ≤
        effectiveGain ratePlastic alphaPlastic :=
    effectiveGain_stable_le_plastic
      rateStable ratePlastic alphaStable alphaPlastic
      rate_order decay_order ratePlastic_nonnegative alphaStable_le_one
  have plastic_factor_nonnegative :
      0 ≤ 1 - effectiveGain ratePlastic alphaPlastic :=
    meanErrorFactor_nonnegative ratePlastic alphaPlastic
      ratePlastic_nonnegative ratePlastic_le_one alphaPlastic_nonnegative
      alphaPlastic_le_one
  have stable_factor_nonnegative :
      0 ≤ 1 - effectiveGain rateStable alphaStable :=
    meanErrorFactor_nonnegative rateStable alphaStable
      rateStable_nonnegative rateStable_le_one alphaStable_nonnegative
      alphaStable_le_one
  rw [abs_of_nonneg plastic_factor_nonnegative,
    abs_of_nonneg stable_factor_nonnegative]
  have factor_order :
      1 - effectiveGain ratePlastic alphaPlastic ≤
        1 - effectiveGain rateStable alphaStable := by
    linarith
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ plastic_factor_nonnegative factor_order steps)
    (norm_nonneg (memory - target))

/-- Equal effective gains make the entire one-step mean map identical. -/
theorem bernoulliMean_eq_of_effectiveGain_eq
    (rate₁ alpha₁ rate₂ alpha₂ : ℝ)
    (gain_equal :
      effectiveGain rate₁ alpha₁ = effectiveGain rate₂ alpha₂)
    (memory target : State) :
    bernoulliMean rate₁ alpha₁ memory target =
      bernoulliMean rate₂ alpha₂ memory target := by
  rw [bernoulliMean_eq_interpolation, bernoulliMean_eq_interpolation,
    gain_equal]

end Update

section BranchVariance

variable [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Finite Bernoulli second moment around the branch mean. -/
def branchVariance
    (rate alpha : ℝ) (memory target : State) : ℝ :=
  (1 - rate) *
      ‖branchUpdate false alpha memory target -
        bernoulliMean rate alpha memory target‖ ^ 2 +
    rate *
      ‖branchUpdate true alpha memory target -
        bernoulliMean rate alpha memory target‖ ^ 2

theorem memory_sub_bernoulliMean
    (rate alpha : ℝ) (memory target : State) :
    memory - bernoulliMean rate alpha memory target =
      (-effectiveGain rate alpha) • (target - memory) := by
  rw [bernoulliMean_eq_interpolation]
  module

theorem emaUpdate_sub_bernoulliMean
    (rate alpha : ℝ) (memory target : State) :
    emaUpdate alpha memory target -
        bernoulliMean rate alpha memory target =
      ((1 - rate) * (1 - alpha)) • (target - memory) := by
  rw [emaUpdate_eq_interpolation, bernoulliMean_eq_interpolation]
  unfold effectiveGain
  module

/-- Exact branch variance of the stochastic EMA.  It vanishes for deterministic
update rates even when the mean interpolation is nontrivial. -/
theorem branchVariance_eq
    (rate alpha : ℝ) (memory target : State)
    (rate_nonnegative : 0 ≤ rate)
    (rate_le_one : rate ≤ 1)
    (alpha_le_one : alpha ≤ 1) :
    branchVariance rate alpha memory target =
      rate * (1 - rate) * (1 - alpha) ^ 2 *
        ‖target - memory‖ ^ 2 := by
  have gain_nonnegative :
      0 ≤ effectiveGain rate alpha :=
    effectiveGain_nonnegative rate alpha rate_nonnegative alpha_le_one
  have rate_complement_nonnegative : 0 ≤ 1 - rate := by linarith
  have alpha_complement_nonnegative : 0 ≤ 1 - alpha := by linarith
  have product_nonnegative :
      0 ≤ (1 - rate) * (1 - alpha) :=
    mul_nonneg rate_complement_nonnegative alpha_complement_nonnegative
  unfold branchVariance
  rw [branchUpdate_false, branchUpdate_true,
    memory_sub_bernoulliMean, emaUpdate_sub_bernoulliMean,
    norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, abs_neg,
    abs_of_nonneg gain_nonnegative, abs_of_nonneg product_nonnegative]
  unfold effectiveGain
  ring

end BranchVariance

/-! ## Executable boundaries -/

/-- Positive fixture: with a fixed scalar target, the plastic memory has
error factor `1 / 2`, while the stable memory has factor `7 / 8`. -/
theorem plastic_and_stable_three_step :
    meanIterate (1 : ℝ) (1 / 2 : ℝ) (0 : ℝ) 3 1 = 1 / 8 ∧
      meanIterate (1 / 2 : ℝ) (3 / 4 : ℝ) (0 : ℝ) 3 1 = 343 / 512 := by
  norm_num [meanIterate, bernoulliMean, emaUpdate]

/-- Negative boundary: decay ordering alone does not make the nominal plastic
memory faster when its update probability is lower. -/
theorem decay_order_alone_is_insufficient :
    (0 : ℝ) ≤ 1 / 2 ∧
      effectiveGain 0 0 <
        effectiveGain 1 (1 / 2) := by
  norm_num [effectiveGain]

/-- Negative boundary: update-rate ordering alone does not make the nominal
plastic memory faster when its decay is too large. -/
theorem rate_order_alone_is_insufficient :
    (1 / 2 : ℝ) ≤ 1 ∧
      effectiveGain 1 1 <
        effectiveGain (1 / 2) 0 := by
  norm_num [effectiveGain]

/-- Two distinct stochastic parameter pairs induce the same mean gain. -/
theorem distinct_parameters_same_effectiveGain :
    ((1 / 2 : ℝ), (1 / 2 : ℝ)) ≠ ((1 : ℝ), (3 / 4 : ℝ)) ∧
      effectiveGain (1 / 2) (1 / 2) =
        effectiveGain 1 (3 / 4) := by
  norm_num [effectiveGain]

/-- The same-mean pairs remain distinguishable by branch variance. -/
theorem same_mean_different_branch_variance :
    branchVariance (1 / 2 : ℝ) (1 / 2 : ℝ) (0 : ℝ) (1 : ℝ) = 1 / 16 ∧
      branchVariance (1 : ℝ) (3 / 4 : ℝ) (0 : ℝ) (1 : ℝ) = 0 := by
  norm_num
    [branchVariance, branchUpdate, bernoulliMean, emaUpdate, Real.norm_eq_abs]

end

end StochasticSemanticMemory

end Mettapedia.MachineLearning.ContinualLearning

#print axioms Mettapedia.MachineLearning.ContinualLearning.StochasticSemanticMemory.meanIterate_sub_target
#print axioms Mettapedia.MachineLearning.ContinualLearning.StochasticSemanticMemory.plastic_mean_error_le_stable
#print axioms Mettapedia.MachineLearning.ContinualLearning.StochasticSemanticMemory.branchVariance_eq
#print axioms Mettapedia.MachineLearning.ContinualLearning.StochasticSemanticMemory.decay_order_alone_is_insufficient
#print axioms Mettapedia.MachineLearning.ContinualLearning.StochasticSemanticMemory.same_mean_different_branch_variance
