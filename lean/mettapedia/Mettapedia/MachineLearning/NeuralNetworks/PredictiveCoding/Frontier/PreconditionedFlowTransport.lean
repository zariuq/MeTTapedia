import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.DeepLineRestriction
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# General chart transport for Euclidean gradient flow

An invertible smooth chart preserves energy values, critical points, and the
negative index of a Hessian quadratic form.  It does not generally conjugate
ordinary Euclidean gradient flow.  At a point where the chart Jacobian is
`J`, the pulled-back gradient is `J† g`; pushing its negative gradient flow
forward gives `-(J J†) g`.  Thus raw Euclidean flow conjugacy holds exactly
when `J J†` is the identity.

The result is pointwise and applies at every point of a smooth chart by
instantiating its Fréchet derivative there.  No global linearity of the chart
is assumed.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Filter
open scoped InnerProduct InnerProductSpace

section ChartGradient

variable {Error State : Type*}
variable [NormedAddCommGroup Error] [InnerProductSpace ℝ Error] [CompleteSpace Error]
variable [NormedAddCommGroup State] [InnerProductSpace ℝ State] [CompleteSpace State]

/-- The error-coordinate Euclidean gradient is the adjoint-Jacobian pullback
of the state-coordinate gradient. -/
theorem chart_gradient_transport
    (chart : Error → State) (energy : State → ℝ)
    (error : Error) (stateGradient : State)
    (jacobian : Error ≃L[ℝ] State)
    (hchart : HasFDerivAt chart (jacobian : Error →L[ℝ] State) error)
    (henergy : HasGradientAt energy stateGradient (chart error)) :
    HasGradientAt (energy ∘ chart)
      (((jacobian : Error →L[ℝ] State)†) stateGradient) error := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hcomp := henergy.hasFDerivAt.comp error hchart
  have hderivative :
      InnerProductSpace.toDual ℝ Error
          (((jacobian : Error →L[ℝ] State)†) stateGradient) =
        InnerProductSpace.toDual ℝ State stateGradient ∘SL
          (jacobian : Error →L[ℝ] State) := by
    ext direction
    exact ContinuousLinearMap.adjoint_inner_left
      (jacobian : Error →L[ℝ] State) direction stateGradient
  rw [hderivative]
  exact hcomp

/-- Negative Euclidean gradient flow in chart coordinates. -/
noncomputable def chartErrorGradientFlow
    (jacobian : Error ≃L[ℝ] State) (stateGradient : State) : Error :=
  -(((jacobian : Error →L[ℝ] State)†) stateGradient)

/-- Push a chart-coordinate velocity into state coordinates. -/
def chartVelocityPushforward
    (jacobian : Error ≃L[ℝ] State) (velocity : Error) : State :=
  jacobian velocity

/-- The metric preconditioner induced in state coordinates by a chart. -/
noncomputable def chartJJtApply
    (jacobian : Error ≃L[ℝ] State) (stateVector : State) : State :=
  jacobian (((jacobian : Error →L[ℝ] State)†) stateVector)

/-- Exact generalization of the shear calculation: pushing chart-coordinate
gradient flow forward gives the `J J†`-preconditioned state flow. -/
theorem chart_errorFlow_pushforward_eq_preconditioned_stateFlow
    (jacobian : Error ≃L[ℝ] State) (stateGradient : State) :
    chartVelocityPushforward jacobian
        (chartErrorGradientFlow jacobian stateGradient) =
      -(chartJJtApply jacobian stateGradient) := by
  simp [chartVelocityPushforward, chartErrorGradientFlow, chartJJtApply]

/-- Raw Euclidean gradient flows are conjugate for every possible state
gradient exactly when the induced `J J†` metric factor is the identity. -/
theorem chart_rawGradientFlow_conjugate_iff_JJt_identity
    (jacobian : Error ≃L[ℝ] State) :
    (∀ stateGradient,
      chartVelocityPushforward jacobian
          (chartErrorGradientFlow jacobian stateGradient) = -stateGradient) ↔
      (jacobian : Error →L[ℝ] State) ∘L
          ((jacobian : Error →L[ℝ] State)†) =
        ContinuousLinearMap.id ℝ State := by
  constructor
  · intro h
    ext stateGradient
    simpa [chartVelocityPushforward, chartErrorGradientFlow] using h stateGradient
  · intro h stateGradient
    have happ := DFunLike.congr_fun h stateGradient
    simpa [chartVelocityPushforward, chartErrorGradientFlow] using
      congrArg Neg.neg happ

/-- Invertibility of the chart Jacobian makes its adjoint injective. -/
theorem chart_adjoint_apply_eq_zero_iff
    (jacobian : Error ≃L[ℝ] State) (stateVector : State) :
    ((jacobian : Error →L[ℝ] State)†) stateVector = 0 ↔ stateVector = 0 := by
  constructor
  · intro hzero
    have hinner : ⟪stateVector, stateVector⟫_ℝ = 0 := by
      calc
        ⟪stateVector, stateVector⟫_ℝ =
            ⟪stateVector,
              (jacobian : Error →L[ℝ] State) (jacobian.symm stateVector)⟫_ℝ := by
          simp
        _ = ⟪((jacobian : Error →L[ℝ] State)†) stateVector,
              jacobian.symm stateVector⟫_ℝ := by
            rw [ContinuousLinearMap.adjoint_inner_left]
        _ = 0 := by simp [hzero]
    exact inner_self_eq_zero.mp hinner
  · rintro rfl
    simp

/-- Corresponding points are critical simultaneously.  This statement uses
actual gradient witnesses, rather than only comparing abstract differentials. -/
theorem chart_critical_points_correspond
    (chart : Error → State) (energy : State → ℝ)
    (error : Error) (stateGradient : State)
    (jacobian : Error ≃L[ℝ] State)
    (hchart : HasFDerivAt chart (jacobian : Error →L[ℝ] State) error)
    (henergy : HasGradientAt energy stateGradient (chart error)) :
    HasGradientAt (energy ∘ chart) 0 error ↔ stateGradient = 0 := by
  have hpull := chart_gradient_transport chart energy error stateGradient
    jacobian hchart henergy
  constructor
  · intro hcritical
    have hgrad : ((jacobian : Error →L[ℝ] State)†) stateGradient = 0 :=
      hpull.unique hcritical
    exact (chart_adjoint_apply_eq_zero_iff jacobian stateGradient).mp hgrad
  · intro hzero
    subst stateGradient
    simpa using hpull

end ChartGradient

section HessianIndex

variable {Error State : Type*}
variable [AddCommGroup Error] [Module ℝ Error]
variable [AddCommGroup State] [Module ℝ State]

/-- Sylvester inertia under the invertible Jacobian: the pulled-back Hessian
has exactly the same number of negative directions. -/
theorem chart_hessian_negativeIndex_invariant
    (jacobian : Error ≃ₗ[ℝ] State) (hessian : QuadraticForm ℝ State) :
    sigNeg
        (hessian.comp (jacobian : Error →ₗ[ℝ] State)) =
      sigNeg hessian := by
  have hequivalent :
      hessian.Equivalent
        (hessian.comp (jacobian : Error →ₗ[ℝ] State)) :=
    ⟨QuadraticMap.isometryEquivOfCompLinearEquiv hessian jacobian⟩
  exact hequivalent.sigNeg_eq.symm

end HessianIndex

/-! ## Positive and negative fixtures -/

/-- The identity chart has no metric distortion. -/
theorem identityChart_JJt_positiveExample :
    (((ContinuousLinearEquiv.refl ℝ ℝ : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) ∘L
        (((ContinuousLinearEquiv.refl ℝ ℝ : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ)†)) =
      ContinuousLinearMap.id ℝ ℝ := by
  simp

/-- The previously checked shear is the concrete negative fixture for the
general theorem: its non-orthogonal chart does not conjugate raw flows. -/
theorem nonOrthogonalChart_rawFlow_negativeExample :
    shearPushforward (shearErrorGradientFlow (1, 0)) ≠
      shearStateGradientFlow (shearToState (1, 0)) :=
  shear_euclidean_gradient_flows_not_conjugate

/-- Crown combining gradient transport, the exact conjugacy boundary,
critical-point correspondence, and Hessian-index invariance. -/
theorem generalChart_transport_crown
    {Error State : Type*}
    [NormedAddCommGroup Error] [InnerProductSpace ℝ Error] [CompleteSpace Error]
    [NormedAddCommGroup State] [InnerProductSpace ℝ State] [CompleteSpace State]
    (chart : Error → State) (energy : State → ℝ)
    (error : Error) (stateGradient : State)
    (jacobian : Error ≃L[ℝ] State)
    (hchart : HasFDerivAt chart (jacobian : Error →L[ℝ] State) error)
    (henergy : HasGradientAt energy stateGradient (chart error)) :
    HasGradientAt (energy ∘ chart)
        (((jacobian : Error →L[ℝ] State)†) stateGradient) error ∧
      chartVelocityPushforward jacobian
          (chartErrorGradientFlow jacobian stateGradient) =
        -(chartJJtApply jacobian stateGradient) ∧
      (HasGradientAt (energy ∘ chart) 0 error ↔ stateGradient = 0) := by
  exact ⟨chart_gradient_transport chart energy error stateGradient jacobian
      hchart henergy,
    chart_errorFlow_pushforward_eq_preconditioned_stateFlow jacobian stateGradient,
    chart_critical_points_correspond chart energy error stateGradient jacobian
      hchart henergy⟩

#print axioms generalChart_transport_crown
#print axioms chart_rawGradientFlow_conjugate_iff_JJt_identity
#print axioms chart_hessian_negativeIndex_invariant

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
