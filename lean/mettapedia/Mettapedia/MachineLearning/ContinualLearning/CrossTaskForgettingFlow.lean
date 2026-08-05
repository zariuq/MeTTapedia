import Mathlib

/-!
# Cross-task kernel flow and instantaneous forgetting

Graldi et al., *The Importance of Being Lazy: Scaling Limits of Continual
Learning* (ICML 2025, arXiv:2506.16884), Equation (12), express the
instantaneous change of an old task's half-squared residual during new-task
training as the negative pairing between the old residual and the new
residual transported through the cross-task neural tangent kernel.

This file recovers that differential identity for arbitrary real inner-product
spaces and continuous linear cross-task transports. It also proves an
operator-norm budget, the exact sign boundary, and a positive-semidefinite
two-task kernel fixture whose forgetting sign changes when only the new-task
residual sign changes.

The source's dynamical mean-field limit, Gaussian-process construction,
self-consistent kernel equations, lazy--rich transition, finite-width
approximation, and empirical optimum are not proved here. The derivative
theorem applies after a concrete residual trajectory has been shown to obey
the declared cross-task flow at the point in question.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace CrossTaskForgettingFlow

noncomputable section

open scoped InnerProductSpace

variable {OldError NewError : Type*}
  [NormedAddCommGroup OldError] [InnerProductSpace ℝ OldError]
  [NormedAddCommGroup NewError] [InnerProductSpace ℝ NewError]

/-- The old task's half-squared residual energy. -/
def oldTaskEnergy (error : OldError) : ℝ :=
  ‖error‖ ^ 2 / 2

/-- The source-shaped instantaneous forgetting rate: the negative old/new
residual pairing after cross-task kernel transport. -/
def crossTaskForgettingRate
    (oldError : OldError)
    (crossKernel : NewError →L[ℝ] OldError)
    (newError : NewError) : ℝ :=
  -⟪oldError, crossKernel newError⟫_ℝ

/-- Differential source correspondence. If the old residual evolves by the
negative cross-kernel transport of the current new residual, then the
old-task energy derivative is exactly the cross-task forgetting rate. -/
theorem oldTaskEnergy_hasDerivAt_crossTaskForgettingRate
    (oldError : ℝ → OldError)
    (newError : NewError)
    (crossKernel : NewError →L[ℝ] OldError)
    (time : ℝ)
    (evolution :
      HasDerivAt oldError (-(crossKernel newError)) time) :
    HasDerivAt
      (fun t => oldTaskEnergy (oldError t))
      (crossTaskForgettingRate
        (oldError time) crossKernel newError)
      time := by
  have halfDerivative :=
    evolution.norm_sq.mul_const (1 / 2 : ℝ)
  have coefficientIdentity :
      2 * ⟪oldError time, -(crossKernel newError)⟫_ℝ *
          (1 / 2 : ℝ) =
        crossTaskForgettingRate
          (oldError time) crossKernel newError := by
    rw [inner_neg_right]
    unfold crossTaskForgettingRate
    ring
  have energyDerivative :=
    halfDerivative.congr_deriv coefficientIdentity
  simpa [oldTaskEnergy, div_eq_mul_inv] using energyDerivative

/-- The sign of the cross pairing is the exact instantaneous boundary:
negative pairing means positive forgetting rate. -/
theorem crossTaskForgettingRate_pos_iff
    (oldError : OldError)
    (crossKernel : NewError →L[ℝ] OldError)
    (newError : NewError) :
    0 < crossTaskForgettingRate oldError crossKernel newError ↔
      ⟪oldError, crossKernel newError⟫_ℝ < 0 := by
  simp [crossTaskForgettingRate]

/-- Positive cross pairing means the old-task energy is instantaneously
decreasing. -/
theorem crossTaskForgettingRate_neg_iff
    (oldError : OldError)
    (crossKernel : NewError →L[ℝ] OldError)
    (newError : NewError) :
    crossTaskForgettingRate oldError crossKernel newError < 0 ↔
      0 < ⟪oldError, crossKernel newError⟫_ℝ := by
  simp [crossTaskForgettingRate]

/-- Orthogonal transported residuals have zero instantaneous forgetting. -/
theorem crossTaskForgettingRate_eq_zero_of_inner_eq_zero
    (oldError : OldError)
    (crossKernel : NewError →L[ℝ] OldError)
    (newError : NewError)
    (orthogonal :
      ⟪oldError, crossKernel newError⟫_ℝ = 0) :
    crossTaskForgettingRate oldError crossKernel newError = 0 := by
  simp [crossTaskForgettingRate, orthogonal]

/-- A zero cross-task kernel has zero instantaneous forgetting for every
pair of task residuals. -/
theorem zeroCrossKernel_has_zero_forgettingRate
    (oldError : OldError)
    (newError : NewError) :
    crossTaskForgettingRate
      oldError (0 : NewError →L[ℝ] OldError) newError = 0 := by
  simp [crossTaskForgettingRate]

/-- Operator-norm budget for the magnitude of instantaneous forgetting. -/
theorem abs_crossTaskForgettingRate_le
    (oldError : OldError)
    (crossKernel : NewError →L[ℝ] OldError)
    (newError : NewError) :
    |crossTaskForgettingRate oldError crossKernel newError| ≤
      ‖oldError‖ * (‖crossKernel‖ * ‖newError‖) := by
  unfold crossTaskForgettingRate
  rw [abs_neg]
  calc
    |⟪oldError, crossKernel newError⟫_ℝ| ≤
        ‖oldError‖ * ‖crossKernel newError‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖oldError‖ * (‖crossKernel‖ * ‖newError‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.le_opNorm crossKernel newError)
        (norm_nonneg _)

/-! ## Positive-semidefinite kernel boundary -/

/-- Scalar cross-task transport used by the executable fixtures. -/
def scalarCrossKernel (coupling : ℝ) : ℝ →L[ℝ] ℝ :=
  coupling • ContinuousLinearMap.id ℝ ℝ

/-- Quadratic form of a symmetric two-task scalar kernel with unit diagonal
and off-diagonal `coupling`. -/
def jointKernelQuadratic
    (coupling oldError newError : ℝ) : ℝ :=
  oldError ^ 2 +
    2 * coupling * oldError * newError +
    newError ^ 2

/-- Coupling one half gives a positive-semidefinite joint two-task kernel. -/
theorem halfCoupling_jointKernel_nonnegative
    (oldError newError : ℝ) :
    0 ≤ jointKernelQuadratic (1 / 2) oldError newError := by
  unfold jointKernelQuadratic
  nlinarith [
    sq_nonneg (oldError + newError),
    sq_nonneg (oldError - newError)
  ]

/-- Even with that positive-semidefinite joint kernel, opposite task
residuals give a positive instantaneous forgetting rate. -/
theorem halfCoupling_opposite_errors_forget :
    crossTaskForgettingRate
      (1 : ℝ) (scalarCrossKernel (1 / 2)) (-1) =
        1 / 2 := by
  norm_num [crossTaskForgettingRate, scalarCrossKernel]

/-- With the same kernel and equal residual norms, aligned task residuals
give an equally large negative rate instead. -/
theorem halfCoupling_aligned_errors_transfer :
    crossTaskForgettingRate
      (1 : ℝ) (scalarCrossKernel (1 / 2)) 1 =
        -(1 / 2) := by
  norm_num [crossTaskForgettingRate, scalarCrossKernel]

/-- Positive semidefiniteness of the joint kernel does not determine the
sign of forgetting: residual orientation remains load-bearing. -/
theorem positiveSemidefinite_jointKernel_allows_both_rate_signs :
    (∀ oldError newError : ℝ,
      0 ≤ jointKernelQuadratic (1 / 2) oldError newError) ∧
      crossTaskForgettingRate
          (1 : ℝ) (scalarCrossKernel (1 / 2)) (-1) =
        1 / 2 ∧
      crossTaskForgettingRate
          (1 : ℝ) (scalarCrossKernel (1 / 2)) 1 =
        -(1 / 2) := by
  exact ⟨halfCoupling_jointKernel_nonnegative,
    halfCoupling_opposite_errors_forget,
    halfCoupling_aligned_errors_transfer⟩

#print axioms oldTaskEnergy_hasDerivAt_crossTaskForgettingRate
#print axioms crossTaskForgettingRate_pos_iff
#print axioms abs_crossTaskForgettingRate_le
#print axioms zeroCrossKernel_has_zero_forgettingRate
#print axioms positiveSemidefinite_jointKernel_allows_both_rate_signs

end

end CrossTaskForgettingFlow

end Mettapedia.MachineLearning.ContinualLearning
