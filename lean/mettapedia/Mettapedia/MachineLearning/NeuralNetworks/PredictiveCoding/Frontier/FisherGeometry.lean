import Mettapedia.MachineLearning.ContinualLearning.MinimumChangeUpdate
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Fisher geometry of precision-weighted predictive coding

This file separates the exact linear-Gaussian identity from the approximation
steps used in nonlinear predictive-coding implementations.  For an affine
Gaussian layer, the weight Fisher is the Kronecker product of the output
precision and the activation second moment.  Scalar precision is therefore
exact only when the omitted activation geometry is isotropic (or happens not
to affect the requested direction).

The second half records the approximation ladder and proves a relative-metric
perturbation bound for natural directions.  No nonlinear network is identified
with its local Gaussian model.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped BigOperators InnerProductSpace

/-! ## Exact finite linear-Gaussian layer -/

section GaussianLayer

variable {Sample Input Output : Type*} [Fintype Sample]

/-- Weighted activation second moment.  Probability normalization is not
needed for the factorization: it is an algebraic identity for every finite
nonnegative or signed weighting. -/
noncomputable def activationSecondMoment
    (weight : Sample → ℝ) (activation : Sample → Input → ℝ) :
    Matrix Input Input ℝ :=
  fun i j => ∑ sample, weight sample * activation sample i * activation sample j

/-- Weight-space Fisher entries of a correctly specified conditional Gaussian
layer with fixed output precision.  These are the expected Gaussian NLL
curvatures with respect to the entries of the affine weight matrix. -/
noncomputable def gaussianWeightFisher
    (weight : Sample → ℝ) (activation : Sample → Input → ℝ)
    (precision : Matrix Output Output ℝ) :
    Matrix (Output × Input) (Output × Input) ℝ :=
  fun row column =>
    ∑ sample, weight sample * precision row.1 column.1 *
      activation sample row.2 * activation sample column.2

/-- The exact Gaussian weight Fisher is output precision Kronecker activation
second moment. -/
theorem gaussianWeightFisher_eq_kronecker
    (weight : Sample → ℝ) (activation : Sample → Input → ℝ)
    (precision : Matrix Output Output ℝ) :
    gaussianWeightFisher weight activation precision =
      precision.kronecker (activationSecondMoment weight activation) := by
  ext row column
  rcases row with ⟨outputRow, inputRow⟩
  rcases column with ⟨outputColumn, inputColumn⟩
  change (∑ sample, weight sample * precision outputRow outputColumn *
      activation sample inputRow * activation sample inputColumn) =
    precision outputRow outputColumn *
      (∑ sample, weight sample * activation sample inputRow *
        activation sample inputColumn)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample _
  ring

end GaussianLayer

section NaturalStep

variable {Input Output : Type*} [Fintype Input] [DecidableEq Input]
  [Fintype Output] [DecidableEq Output]

/-- Two-sided natural direction for a Kronecker-factored Gaussian layer. -/
noncomputable def twoSidedNaturalStep
    (precisionInv : Matrix Output Output ℝ)
    (gradient : Matrix Output Input ℝ)
    (activationInv : Matrix Input Input ℝ) : Matrix Output Input ℝ :=
  -(precisionInv * gradient * activationInv)

/-- The two-sided direction solves the exact Kronecker normal equation when
the supplied factors are the appropriate one-sided inverses. -/
theorem twoSidedNaturalStep_solves
    (precision precisionInv : Matrix Output Output ℝ)
    (activation activationInv : Matrix Input Input ℝ)
    (gradient : Matrix Output Input ℝ)
    (hprecision : precision * precisionInv = 1)
    (hactivation : activationInv * activation = 1) :
    precision * twoSidedNaturalStep precisionInv gradient activationInv *
        activation = -gradient := by
  simp only [twoSidedNaturalStep, Matrix.mul_neg, Matrix.neg_mul]
  congr 1
  calc
    precision * (precisionInv * gradient * activationInv) * activation =
        (precision * precisionInv) * gradient *
          (activationInv * activation) := by
      simp only [Matrix.mul_assoc]
    _ = gradient := by rw [hprecision, hactivation, Matrix.one_mul,
      Matrix.mul_one]

/-- Whitened activations and unit scalar precision reduce the natural step to
the negative ordinary gradient. -/
@[simp] theorem twoSidedNaturalStep_unit_factors
    (gradient : Matrix Output Input ℝ) :
    twoSidedNaturalStep (1 : Matrix Output Output ℝ) gradient
      (1 : Matrix Input Input ℝ) = -gradient := by
  simp [twoSidedNaturalStep]

end NaturalStep

/-! ### Correlated-activation counterexample -/

noncomputable def correlatedActivationMoment : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, (1 / 2 : ℝ); (1 / 2 : ℝ), 1]

noncomputable def correlatedGradient : Matrix (Fin 1) (Fin 2) ℝ :=
  !![1, 0]

noncomputable def correlatedNaturalStep : Matrix (Fin 1) (Fin 2) ℝ :=
  !![-(4 / 3 : ℝ), (2 / 3 : ℝ)]

noncomputable def scalarPrecisionOnlyStep (scale : ℝ) :
    Matrix (Fin 1) (Fin 2) ℝ :=
  !![-scale, 0]

/-- The displayed correlated direction solves the activation-side natural
normal equation. -/
theorem correlatedNaturalStep_solves :
    correlatedNaturalStep * correlatedActivationMoment = -correlatedGradient := by
  ext i j
  fin_cases i
  fin_cases j <;>
    norm_num [correlatedNaturalStep, correlatedActivationMoment,
      correlatedGradient, Matrix.mul_apply, Fin.sum_univ_two]

/-- No scalar precision rescaling of the ordinary gradient can recover the
natural direction when the activation covariance is correlated. -/
theorem scalarPrecision_cannot_recover_correlatedNaturalStep
    (scale : ℝ) :
    scalarPrecisionOnlyStep scale ≠ correlatedNaturalStep := by
  intro h
  have hcoordinate := congr_fun (congr_fun h (0 : Fin 1)) (1 : Fin 2)
  norm_num [scalarPrecisionOnlyStep, correlatedNaturalStep] at hcoordinate

/-! ## Approximation ladder -/

/-- Successive information discarded by scalable Fisher approximations. -/
inductive FisherApproximationLevel
  | full
  | layerBlock
  | kronecker
  | activationOnly
  | diagonal
  | scalarPrecision
  deriving DecidableEq, Repr

/-- A numerical rank used only to state the strict refinement order; it makes
no claim about the error of a particular estimator. -/
def FisherApproximationLevel.informationRank : FisherApproximationLevel → ℕ
  | .full => 5
  | .layerBlock => 4
  | .kronecker => 3
  | .activationOnly => 2
  | .diagonal => 1
  | .scalarPrecision => 0

def FisherApproximationLevel.StrictlyRefines
    (finer coarser : FisherApproximationLevel) : Prop :=
  coarser.informationRank < finer.informationRank

theorem fisherApproximation_strict_ladder :
    FisherApproximationLevel.full.StrictlyRefines .layerBlock ∧
    FisherApproximationLevel.layerBlock.StrictlyRefines .kronecker ∧
    FisherApproximationLevel.kronecker.StrictlyRefines .activationOnly ∧
    FisherApproximationLevel.activationOnly.StrictlyRefines .diagonal ∧
    FisherApproximationLevel.diagonal.StrictlyRefines .scalarPrecision := by
  norm_num [FisherApproximationLevel.StrictlyRefines,
    FisherApproximationLevel.informationRank]

/-! ## Relative SPD metric perturbation -/

section MetricPerturbation

variable {Parameter : Type*} [NormedAddCommGroup Parameter]
  [InnerProductSpace ℝ Parameter]

/-- An invertible symmetric positive-definite metric represented by a
continuous linear equivalence. -/
structure InvertibleSPDMetric (Parameter : Type*)
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] where
  operator : Parameter ≃L[ℝ] Parameter
  symmetric : ∀ x y, ⟪operator x, y⟫_ℝ = ⟪operator y, x⟫_ℝ
  positive : ∀ x, x ≠ 0 → 0 < ⟪operator x, x⟫_ℝ

namespace InvertibleSPDMetric

/-- Forget invertibility while retaining the positive metric used by the
minimum-change continual-learning substrate. -/
noncomputable def toAdapterMetric
    (metric : InvertibleSPDMetric Parameter) :
    Mettapedia.MachineLearning.ContinualLearning.AdapterMetric Parameter where
  operator := metric.operator.toContinuousLinearMap
  symmetric := metric.symmetric
  nonnegative := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact le_of_lt (metric.positive x hx)

/-- Approximation error measured in exact inverse-metric coordinates. -/
def RelativeError
    (exact : InvertibleSPDMetric Parameter)
    (approximate : Parameter →L[ℝ] Parameter) (epsilon : ℝ) : Prop :=
  ∀ x,
    ‖exact.operator.symm (approximate x - exact.operator x)‖ ≤
      epsilon * ‖x‖

/-- Equal right-hand sides turn the relative metric error into a contraction
bound between exact and approximate natural directions. -/
theorem direction_error_le_approximate
    (exact : InvertibleSPDMetric Parameter)
    (approximate : Parameter →L[ℝ] Parameter)
    (epsilon : ℝ) (exactDirection approximateDirection gradient : Parameter)
    (hrelative : exact.RelativeError approximate epsilon)
    (hexact : exact.operator exactDirection = gradient)
    (happroximate : approximate approximateDirection = gradient) :
    ‖approximateDirection - exactDirection‖ ≤
      epsilon * ‖approximateDirection‖ := by
  have hequation : approximateDirection - exactDirection =
      -exact.operator.symm
        (approximate approximateDirection -
          exact.operator approximateDirection) := by
    apply exact.operator.injective
    simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply, map_neg]
    rw [hexact, happroximate]
    module
  rw [hequation, norm_neg]
  exact hrelative approximateDirection

/-- If relative metric error is below one, the approximate natural direction
is within `epsilon / (1 - epsilon)` of the exact direction. -/
theorem direction_error_le_ratio
    (exact : InvertibleSPDMetric Parameter)
    (approximate : Parameter →L[ℝ] Parameter)
    (epsilon : ℝ) (exactDirection approximateDirection gradient : Parameter)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    (hrelative : exact.RelativeError approximate epsilon)
    (hexact : exact.operator exactDirection = gradient)
    (happroximate : approximate approximateDirection = gradient) :
    ‖approximateDirection - exactDirection‖ ≤
      epsilon / (1 - epsilon) * ‖exactDirection‖ := by
  have hcontraction := exact.direction_error_le_approximate approximate epsilon
    exactDirection approximateDirection gradient hrelative hexact happroximate
  have htriangle : ‖approximateDirection‖ ≤
      ‖approximateDirection - exactDirection‖ + ‖exactDirection‖ := by
    have h := norm_add_le (approximateDirection - exactDirection) exactDirection
    simpa using h
  have hone : 0 < 1 - epsilon := by linarith
  have hscaled : (1 - epsilon) *
      ‖approximateDirection - exactDirection‖ ≤
        epsilon * ‖exactDirection‖ := by
    nlinarith [mul_le_mul_of_nonneg_left htriangle hepsilon0]
  rw [show epsilon / (1 - epsilon) * ‖exactDirection‖ =
      (epsilon * ‖exactDirection‖) / (1 - epsilon) by field_simp]
  exact (le_div_iff₀ hone).2 (by nlinarith)

end InvertibleSPDMetric

end MetricPerturbation

/-! ## Damping boundary fixtures -/

/-- A zero scalar metric cannot solve a nonzero natural normal equation. -/
theorem singularMetric_has_no_unitGradient_solution :
    ¬ ∃ direction : ℝ, 0 * direction = 1 := by
  simp

/-- Positive scalar damping restores a unique solution. -/
theorem dampedScalarMetric_unique
    (damping gradient direction : ℝ) (hdamping : 0 < damping) :
    damping * direction = gradient ↔ direction = gradient / damping := by
  constructor
  · intro h
    exact (eq_div_iff (ne_of_gt hdamping)).2 (by simpa [mul_comm] using h)
  · rintro rfl
    field_simp

/-- Bad conditioning is visible even in one dimension: the unit-gradient
natural direction grows without bound as curvature tends to zero. -/
theorem illConditionedScalar_direction_exceeds
    (curvature bound : ℝ) (hcurvature : 0 < curvature)
    (hsmall : curvature < 1 / bound) (hbound : 0 < bound) :
    bound < 1 / curvature := by
  apply (lt_div_iff₀ hcurvature).2
  simpa [mul_comm] using ((lt_div_iff₀ hbound).mp hsmall)

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
