import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FisherDiagnostic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Fisher pullback for frozen-parent adapters

When the parent network is frozen, a first-order adapter perturbation reaches
the predictive distribution only through the frozen parent Jacobian.  The
adapter Fisher is therefore the pullback `J† F J` of the output Fisher.  This
file constructs that metric, proves its pairing and positive-definiteness
conditions, and specializes the affine adapter layer to the exact Gaussian
Kronecker factors.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped InnerProductSpace
open Mettapedia.MachineLearning.ContinualLearning

section Pullback

variable {Parameter Output : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
  [CompleteSpace Parameter]
  [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
  [CompleteSpace Output]

/-- Pull back an output Fisher metric through the frozen-parent Jacobian. -/
noncomputable def frozenAdapterPullbackMetric
    (outputMetric : AdapterMetric Output)
    (parentJacobian : Parameter →L[ℝ] Output) : AdapterMetric Parameter where
  operator := parentJacobian.adjoint ∘L outputMetric.operator ∘L parentJacobian
  symmetric := by
    intro x y
    simp only [ContinuousLinearMap.comp_apply]
    rw [parentJacobian.adjoint_inner_left,
      parentJacobian.adjoint_inner_left]
    exact outputMetric.symmetric _ _
  nonnegative := by
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    rw [parentJacobian.adjoint_inner_left]
    exact outputMetric.nonnegative _

/-- The pullback pairing is exactly the output Fisher pairing of the induced
output perturbations. -/
@[simp] theorem frozenAdapterPullbackMetric_pair
    (outputMetric : AdapterMetric Output)
    (parentJacobian : Parameter →L[ℝ] Output) (x y : Parameter) :
    (frozenAdapterPullbackMetric outputMetric parentJacobian).pair x y =
      outputMetric.pair (parentJacobian x) (parentJacobian y) := by
  simp [frozenAdapterPullbackMetric, AdapterMetric.pair,
    ContinuousLinearMap.adjoint_inner_left]

/-- Injectivity of the frozen-parent Jacobian and output positive definiteness
make the adapter pullback positive definite. -/
theorem frozenAdapterPullbackMetric_positiveDefinite
    (outputMetric : AdapterMetric Output)
    (parentJacobian : Parameter →L[ℝ] Output)
    (houtput : outputMetric.PositiveDefinite)
    (hjacobian : Function.Injective parentJacobian) :
    (frozenAdapterPullbackMetric outputMetric parentJacobian).PositiveDefinite := by
  intro x hx
  rw [frozenAdapterPullbackMetric_pair]
  apply houtput
  intro hzero
  apply hx
  apply hjacobian
  simpa using hzero

/-- The adapter local KL budget equals the frozen parent's output KL budget. -/
theorem frozenAdapterKLBudget_eq_output
    (outputMetric : AdapterMetric Output)
    (parentJacobian : Parameter →L[ℝ] Output) (update : Parameter) :
    fisherKLBudget (frozenAdapterPullbackMetric outputMetric parentJacobian)
        update =
      fisherKLBudget outputMetric (parentJacobian update) := by
  simp [fisherKLBudget]

/-- Identity frozen parent is the positive fixture: no geometry is lost. -/
theorem identityFrozenParent_preserves_pair
    (outputMetric : AdapterMetric Parameter) (x y : Parameter) :
    (frozenAdapterPullbackMetric outputMetric
      (ContinuousLinearMap.id ℝ Parameter)).pair x y = outputMetric.pair x y := by
  simp

end Pullback

/-! ## Affine adapter Kronecker factors -/

section AffineAdapter

variable {Sample Input Output : Type*}
  [Fintype Sample]

/-- For an affine adapter feeding a frozen Gaussian output model, the adapter
Fisher factors into propagated output precision and adapter-input activation
second moment.  This is the exact frozen-adapter specialization of the
Gaussian-layer theorem. -/
theorem frozenAffineAdapterFisher_eq_propagatedPrecision_kronecker_activation
    (weight : Sample → ℝ) (adapterInput : Sample → Input → ℝ)
    (propagatedOutputPrecision : Matrix Output Output ℝ) :
    gaussianWeightFisher weight adapterInput propagatedOutputPrecision =
      propagatedOutputPrecision.kronecker
        (activationSecondMoment weight adapterInput) :=
  gaussianWeightFisher_eq_kronecker weight adapterInput
    propagatedOutputPrecision

end AffineAdapter

/-! ## Noninjective boundary fixture -/

noncomputable def frozenCoordinateReadout :
    FisherDiagnosticPlane →L[ℝ] ℝ :=
  innerSL ℝ fisherDiagnosticAxis0

theorem frozenCoordinateReadout_axis1_zero :
    frozenCoordinateReadout fisherDiagnosticAxis1 = 0 := by
  rw [frozenCoordinateReadout, innerSL_apply_apply]
  rw [real_inner_comm]
  exact fisherDiagnosticAxes_orthogonal

theorem fisherDiagnosticAxis1_ne_zero : fisherDiagnosticAxis1 ≠ 0 := by
  simp [fisherDiagnosticAxis1]

/-- A noninjective frozen parent makes the pullback Fisher degenerate even when
the output metric is positive definite. -/
theorem noninjectiveFrozenParent_pullback_degenerate :
    fisherDiagnosticAxis1 ≠ 0 ∧
      (frozenAdapterPullbackMetric
        (identityAdapterMetric : AdapterMetric ℝ) frozenCoordinateReadout).pair
          fisherDiagnosticAxis1 fisherDiagnosticAxis1 = 0 := by
  constructor
  · exact fisherDiagnosticAxis1_ne_zero
  · rw [frozenAdapterPullbackMetric_pair,
      frozenCoordinateReadout_axis1_zero]
    simp

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
