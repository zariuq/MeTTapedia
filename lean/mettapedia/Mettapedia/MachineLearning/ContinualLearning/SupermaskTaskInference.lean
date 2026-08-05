import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LogitLossCurvature

/-!
# Supermask superposition and detached task-inference gradients

Wortsman et al., *Supermasks in Superposition* (NeurIPS 2020,
arXiv:2006.14769), combine task masks with real coefficients before applying
a fixed random network.  Their Equation 19 is linear in the mask at the
fixed-feature linear head.  Appendix I, Lemma I.1, then constructs a
task-inference objective by detaching the real output coordinates and applying
log-sum-exp.  Its declared gradient is zero on detached coordinates and
matches the supervised cross-entropy gradient on every superfluous output.

This file isolates both exact finite statements.  The mask-superposition
identity is proved for arbitrary real masks and coefficients.  The gradient
result reuses the exact categorical softmax-minus-one-hot gradient already
defined in `LogitLossCurvature`.

Two boundaries are explicit.  If the supervised target is itself placed in
the superfluous set, the two gradients differ by exactly one at that
coordinate.  Moreover, linear mask superposition does not commute with a
nonlinear activation.  No claim is made here about one-shot task recovery,
expected gradient signs, learned masks, or empirical accuracy; those require
the probabilistic assumptions following Lemma I.1 in the source.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace SupermaskTaskInference

open scoped BigOperators

noncomputable section

/-! ## Weighted superposition at a fixed-feature linear head -/

variable
  {Task Parameter Output Class : Type*}

/-- Pointwise real-valued superposition of task masks.  Binary masks are the
source construction; allowing arbitrary real entries exposes the algebraic
content of the identity. -/
def weightedSupermask
    [Fintype Task]
    (coefficient : Task → ℝ)
    (mask : Task → Parameter → ℝ) :
    Parameter → ℝ :=
  fun parameter => ∑ task, coefficient task * mask task parameter

/-- One output coordinate of a fixed-feature masked linear head. -/
def maskedLinearLogit
    [Fintype Parameter]
    (weight : Parameter → Output → ℝ)
    (mask : Parameter → ℝ)
    (feature : Parameter → ℝ)
    (output : Output) : ℝ :=
  ∑ parameter, weight parameter output * mask parameter * feature parameter

/-- Equation 19 at a fixed-feature linear head: applying the coefficient
superposition of masks equals the corresponding coefficient superposition of
the task-specific logits. -/
theorem maskedLinearLogit_weightedSupermask
    [Fintype Task] [Fintype Parameter]
    (coefficient : Task → ℝ)
    (mask : Task → Parameter → ℝ)
    (weight : Parameter → Output → ℝ)
    (feature : Parameter → ℝ)
    (output : Output) :
    maskedLinearLogit weight
        (weightedSupermask coefficient mask) feature output =
      ∑ task, coefficient task *
        maskedLinearLogit weight (mask task) feature output := by
  classical
  simp only [maskedLinearLogit, weightedSupermask]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro task _
  apply Finset.sum_congr rfl
  intro parameter _
  ring

/-- A one-hot coefficient selects exactly one task mask. -/
theorem weightedSupermask_oneHot
    [Fintype Task] [DecidableEq Task]
    (selected : Task)
    (mask : Task → Parameter → ℝ) :
    weightedSupermask
        (fun task => if task = selected then 1 else 0) mask =
      mask selected := by
  funext parameter
  simp [weightedSupermask]

/-! ## Appendix I's detached log-sum-exp gradient -/

open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
open LogitLossCurvature

variable [Fintype Class] [DecidableEq Class]

/-- The declared reverse gradient of log-sum-exp after the real output
coordinates have been detached.  The forward logits and their normalizer are
unchanged; only coordinates in `superfluous` receive reverse credit. -/
noncomputable def detachedLogSumExpGradient
    (superfluous : Finset Class)
    (logits : LogitVector Class) :
    LogitVector Class :=
  WithLp.toLp 2 fun output =>
    if output ∈ superfluous then
      Real.exp (logits output) / categoricalExpSum logits
    else
      0

@[simp] theorem detachedLogSumExpGradient_apply
    (superfluous : Finset Class)
    (logits : LogitVector Class)
    (output : Class) :
    detachedLogSumExpGradient superfluous logits output =
      if output ∈ superfluous then
        Real.exp (logits output) / categoricalExpSum logits
      else
        0 := by
  simp [detachedLogSumExpGradient]

/-- Restriction of a logit-space vector to the declared superfluous outputs. -/
noncomputable def restrictOutputs
    (superfluous : Finset Class)
    (vector : LogitVector Class) :
    LogitVector Class :=
  WithLp.toLp 2 fun output =>
    if output ∈ superfluous then vector output else 0

@[simp] theorem restrictOutputs_apply
    (superfluous : Finset Class)
    (vector : LogitVector Class)
    (output : Class) :
    restrictOutputs superfluous vector output =
      if output ∈ superfluous then vector output else 0 := by
  simp [restrictOutputs]

/-- Coordinate form of Wortsman et al.'s Lemma I.1: if the supervised target
is a real output, the detached log-sum-exp gradient equals the supervised
cross-entropy gradient on every superfluous output. -/
theorem detachedLogSumExpGradient_eq_crossEntropyGradient_of_mem
    (superfluous : Finset Class)
    (target output : Class)
    (logits : LogitVector Class)
    (target_real : target ∉ superfluous)
    (output_superfluous : output ∈ superfluous) :
    detachedLogSumExpGradient superfluous logits output =
      categoricalCrossEntropyGradient target logits output := by
  have output_ne_target : output ≠ target := by
    intro equality
    apply target_real
    simpa [equality] using output_superfluous
  simp [detachedLogSumExpGradient, categoricalCrossEntropyGradient,
    output_superfluous, output_ne_target]

/-- The complementary half of the construction: detached real outputs receive
zero reverse credit. -/
theorem detachedLogSumExpGradient_eq_zero_of_not_mem
    (superfluous : Finset Class)
    (logits : LogitVector Class)
    (output : Class)
    (output_real : output ∉ superfluous) :
    detachedLogSumExpGradient superfluous logits output = 0 := by
  simp [detachedLogSumExpGradient, output_real]

/-- Vector form of Lemma I.1.  Detaching the real outputs makes the
log-sum-exp gradient exactly the supervised cross-entropy gradient restricted
to the superfluous outputs. -/
theorem detachedLogSumExpGradient_eq_restrict_crossEntropyGradient
    (superfluous : Finset Class)
    (target : Class)
    (logits : LogitVector Class)
    (target_real : target ∉ superfluous) :
    detachedLogSumExpGradient superfluous logits =
      restrictOutputs superfluous
        (categoricalCrossEntropyGradient target logits) := by
  ext output
  by_cases output_superfluous : output ∈ superfluous
  · simp only [restrictOutputs_apply, if_pos output_superfluous]
    exact detachedLogSumExpGradient_eq_crossEntropyGradient_of_mem
      superfluous target output logits target_real output_superfluous
  · simp [detachedLogSumExpGradient, output_superfluous]

/-- Load-bearing negative boundary: if the target is incorrectly declared
superfluous, the detached log-sum-exp and supervised gradients differ by
exactly one at that coordinate. -/
theorem target_superfluous_gradient_difference_eq_one
    (superfluous : Finset Class)
    (target : Class)
    (logits : LogitVector Class)
    (target_superfluous : target ∈ superfluous) :
    detachedLogSumExpGradient superfluous logits target -
        categoricalCrossEntropyGradient target logits target =
      1 := by
  simp [detachedLogSumExpGradient, categoricalCrossEntropyGradient,
    target_superfluous]

/-! ## Executable fixtures and nonlinear boundary -/

abbrev ThreeOutputs := Fin 3

def oneSuperfluous : Finset ThreeOutputs := {2}

def zeroThreeLogits : LogitVector ThreeOutputs :=
  WithLp.toLp 2 fun _ => 0

/-- With class zero as the real target and class two superfluous, the
superfluous gradient agrees exactly with supervised cross-entropy. -/
theorem threeOutput_superfluous_gradient :
    detachedLogSumExpGradient oneSuperfluous zeroThreeLogits 2 =
      categoricalCrossEntropyGradient (0 : ThreeOutputs)
        zeroThreeLogits 2 := by
  exact detachedLogSumExpGradient_eq_crossEntropyGradient_of_mem
    oneSuperfluous 0 2 zeroThreeLogits (by decide) (by decide)

/-- The same fixture gives zero declared reverse credit to the real output
coordinate one. -/
theorem threeOutput_real_gradient_is_detached :
    detachedLogSumExpGradient oneSuperfluous zeroThreeLogits 1 = 0 := by
  exact detachedLogSumExpGradient_eq_zero_of_not_mem
    oneSuperfluous zeroThreeLogits 1 (by decide)

/-- Scalar rectifier used only to expose the nonlinear boundary. -/
def relu (value : ℝ) : ℝ :=
  max value 0

/-- The linear superposition identity cannot be pushed through a nonlinear
activation: the combined logit can cancel even though one task-specific
activated logit is positive. -/
theorem nonlinear_activation_breaks_task_logit_superposition :
    relu ((1 : ℝ) + (-2)) ≠ relu 1 + relu (-2) := by
  norm_num [relu, max_def]

#print axioms maskedLinearLogit_weightedSupermask
#print axioms weightedSupermask_oneHot
#print axioms detachedLogSumExpGradient_eq_crossEntropyGradient_of_mem
#print axioms detachedLogSumExpGradient_eq_zero_of_not_mem
#print axioms detachedLogSumExpGradient_eq_restrict_crossEntropyGradient
#print axioms target_superfluous_gradient_difference_eq_one
#print axioms threeOutput_superfluous_gradient
#print axioms nonlinear_activation_breaks_task_logit_superposition

end

end SupermaskTaskInference

end Mettapedia.MachineLearning.ContinualLearning
