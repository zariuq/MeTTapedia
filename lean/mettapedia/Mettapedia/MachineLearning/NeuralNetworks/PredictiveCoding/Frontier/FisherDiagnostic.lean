import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FisherGeometry

/-!
# Fisher-orthogonal diagnostics for observed neural updates

An update can be Euclidean-distinct from backpropagation without being close
to a natural-gradient direction.  This file decomposes any update into its
Fisher projection onto a nonzero reference direction and an orthogonal
residual.  It proves uniqueness, the Fisher Pythagoras law, the induced local
KL-budget split, and the corresponding quadratic predicted-loss split.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped InnerProductSpace
open Mettapedia.MachineLearning.ContinualLearning

section PairingLemmas

variable {Parameter : Type*} [NormedAddCommGroup Parameter]
  [InnerProductSpace ℝ Parameter]

theorem adapterMetric_pair_smul_left
    (metric : AdapterMetric Parameter) (x y : Parameter) (scalar : ℝ) :
    metric.pair (scalar • x) y = scalar * metric.pair x y := by
  rw [metric.pair_symmetric, metric.pair_smul_right,
    metric.pair_symmetric]

theorem adapterMetric_pair_sub_left
    (metric : AdapterMetric Parameter) (x y z : Parameter) :
    metric.pair (x - y) z = metric.pair x z - metric.pair y z := by
  simp [AdapterMetric.pair, inner_sub_left]

theorem adapterMetric_pair_sub_right
    (metric : AdapterMetric Parameter) (x y z : Parameter) :
    metric.pair x (y - z) = metric.pair x y - metric.pair x z := by
  simp [AdapterMetric.pair, inner_sub_right]

end PairingLemmas

section FisherDecomposition

variable {Parameter : Type*} [NormedAddCommGroup Parameter]
  [InnerProductSpace ℝ Parameter]

/-- Fisher projection coefficient of `update` onto `natural`. -/
noncomputable def fisherProjectionCoefficient
    (metric : AdapterMetric Parameter) (update natural : Parameter) : ℝ :=
  metric.pair update natural / metric.pair natural natural

/-- Component of an observed update Fisher-orthogonal to the reference natural
direction. -/
noncomputable def fisherOrthogonalResidual
    (metric : AdapterMetric Parameter) (update natural : Parameter) : Parameter :=
  update - fisherProjectionCoefficient metric update natural • natural

theorem fisherOrthogonalResidual_decomposition
    (metric : AdapterMetric Parameter) (update natural : Parameter) :
    update = fisherProjectionCoefficient metric update natural • natural +
      fisherOrthogonalResidual metric update natural := by
  simp [fisherOrthogonalResidual]

/-- The constructed residual is exactly Fisher-orthogonal. -/
theorem fisherOrthogonalResidual_orthogonal
    (metric : AdapterMetric Parameter) (update natural : Parameter)
    (hpositive : metric.PositiveDefinite) (hnatural : natural ≠ 0) :
    metric.pair (fisherOrthogonalResidual metric update natural) natural = 0 := by
  have hdenomPos : 0 < metric.pair natural natural :=
    hpositive natural hnatural
  have hdenom : metric.pair natural natural ≠ 0 := ne_of_gt hdenomPos
  rw [fisherOrthogonalResidual, adapterMetric_pair_sub_left,
    adapterMetric_pair_smul_left]
  unfold fisherProjectionCoefficient
  field_simp
  ring

/-- The Fisher-parallel coefficient and orthogonal residual are unique. -/
theorem fisherOrthogonal_decomposition_unique
    (metric : AdapterMetric Parameter) (update natural residual : Parameter)
    (coefficient : ℝ)
    (hpositive : metric.PositiveDefinite) (hnatural : natural ≠ 0)
    (hdecomposition : update = coefficient • natural + residual)
    (horthogonal : metric.pair residual natural = 0) :
    coefficient = fisherProjectionCoefficient metric update natural ∧
      residual = fisherOrthogonalResidual metric update natural := by
  have hdenomPos : 0 < metric.pair natural natural :=
    hpositive natural hnatural
  have hpair : metric.pair update natural =
      coefficient * metric.pair natural natural := by
    rw [hdecomposition, metric.pair_add_left,
      adapterMetric_pair_smul_left, horthogonal, add_zero]
  have hcoefficient : coefficient =
      fisherProjectionCoefficient metric update natural := by
    unfold fisherProjectionCoefficient
    rw [hpair]
    field_simp
  constructor
  · exact hcoefficient
  · rw [fisherOrthogonalResidual, ← hcoefficient, hdecomposition]
    abel

/-- Fisher Pythagoras law for the unique decomposition. -/
theorem fisherOrthogonalResidual_pythagoras
    (metric : AdapterMetric Parameter) (update natural : Parameter)
    (hpositive : metric.PositiveDefinite) (hnatural : natural ≠ 0) :
    metric.pair update update =
      fisherProjectionCoefficient metric update natural ^ 2 *
          metric.pair natural natural +
        metric.pair (fisherOrthogonalResidual metric update natural)
          (fisherOrthogonalResidual metric update natural) := by
  let coefficient := fisherProjectionCoefficient metric update natural
  let residual := fisherOrthogonalResidual metric update natural
  have hdecomposition : update = coefficient • natural + residual := by
    exact fisherOrthogonalResidual_decomposition metric update natural
  have horthogonal : metric.pair residual natural = 0 := by
    exact fisherOrthogonalResidual_orthogonal metric update natural
      hpositive hnatural
  have hreverse : metric.pair natural residual = 0 := by
    rw [metric.pair_symmetric]
    exact horthogonal
  change metric.pair update update =
    coefficient ^ 2 * metric.pair natural natural +
      metric.pair residual residual
  rw [hdecomposition, metric.pair_add_left, metric.pair_add_right,
    metric.pair_add_right, metric.pair_smul_self,
    adapterMetric_pair_smul_left, metric.pair_smul_right,
    horthogonal, hreverse]
  ring

/-- Quadratic local KL budget induced by a Fisher metric. -/
noncomputable def fisherKLBudget
    (metric : AdapterMetric Parameter) (update : Parameter) : ℝ :=
  metric.pair update update / 2

theorem fisherKLBudget_decomposition
    (metric : AdapterMetric Parameter) (update natural : Parameter)
    (hpositive : metric.PositiveDefinite) (hnatural : natural ≠ 0) :
    fisherKLBudget metric update =
      fisherProjectionCoefficient metric update natural ^ 2 / 2 *
          metric.pair natural natural +
        fisherKLBudget metric
          (fisherOrthogonalResidual metric update natural) := by
  rw [fisherKLBudget, fisherKLBudget,
    fisherOrthogonalResidual_pythagoras metric update natural hpositive hnatural]
  ring

/-- A reference direction is natural for `gradient` when the gradient
functional is the negative Fisher pairing with that direction. -/
def IsNaturalDirection
    (metric : AdapterMetric Parameter) (gradient natural : Parameter) : Prop :=
  ∀ direction, ⟪gradient, direction⟫_ℝ = -metric.pair natural direction

/-- Second-order predicted loss change in the Fisher quadratic model. -/
noncomputable def fisherPredictedChange
    (metric : AdapterMetric Parameter) (gradient update : Parameter) : ℝ :=
  ⟪gradient, update⟫_ℝ + fisherKLBudget metric update

/-- Predicted change splits into progress along the natural direction and a
nonnegative Fisher-orthogonal cost. -/
theorem fisherPredictedChange_decomposition
    (metric : AdapterMetric Parameter) (gradient update natural : Parameter)
    (hpositive : metric.PositiveDefinite) (hnatural : natural ≠ 0)
    (hgradient : IsNaturalDirection metric gradient natural) :
    fisherPredictedChange metric gradient update =
      (fisherProjectionCoefficient metric update natural ^ 2 / 2 -
          fisherProjectionCoefficient metric update natural) *
          metric.pair natural natural +
        fisherKLBudget metric
          (fisherOrthogonalResidual metric update natural) := by
  let coefficient := fisherProjectionCoefficient metric update natural
  let residual := fisherOrthogonalResidual metric update natural
  have hdecomposition : update = coefficient • natural + residual := by
    exact fisherOrthogonalResidual_decomposition metric update natural
  have horthogonal : metric.pair residual natural = 0 := by
    exact fisherOrthogonalResidual_orthogonal metric update natural
      hpositive hnatural
  have hreverse : metric.pair natural residual = 0 := by
    rw [metric.pair_symmetric]
    exact horthogonal
  have hkl : fisherKLBudget metric update =
      coefficient ^ 2 / 2 * metric.pair natural natural +
        fisherKLBudget metric residual := by
    simpa [coefficient, residual] using
      fisherKLBudget_decomposition metric update natural hpositive hnatural
  have hpair : metric.pair natural update =
      coefficient * metric.pair natural natural := by
    rw [hdecomposition, metric.pair_add_right, metric.pair_smul_right,
      hreverse, add_zero]
  change fisherPredictedChange metric gradient update =
    (coefficient ^ 2 / 2 - coefficient) *
        metric.pair natural natural + fisherKLBudget metric residual
  rw [fisherPredictedChange, hgradient update, hpair, hkl]
  ring

end FisherDecomposition

/-! ## Concrete fixtures -/

section Fixtures

variable {Parameter : Type*} [NormedAddCommGroup Parameter]
  [InnerProductSpace ℝ Parameter]

/-- Identity Fisher metric. -/
noncomputable def identityAdapterMetric : AdapterMetric Parameter where
  operator := ContinuousLinearMap.id ℝ Parameter
  symmetric := by
    intro x y
    simp only [ContinuousLinearMap.id_apply]
    exact (real_inner_comm x y).symm
  nonnegative := by
    intro x
    rw [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
    exact sq_nonneg _

@[simp] theorem identityAdapterMetric_pair (x y : Parameter) :
    (identityAdapterMetric : AdapterMetric Parameter).pair x y = ⟪x, y⟫_ℝ := by
  simp [identityAdapterMetric, AdapterMetric.pair]

theorem identityAdapterMetric_positiveDefinite :
    (identityAdapterMetric : AdapterMetric Parameter).PositiveDefinite := by
  intro x hx
  rw [identityAdapterMetric_pair, real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)

end Fixtures

abbrev FisherDiagnosticPlane := EuclideanSpace ℝ (Fin 2)

noncomputable def fisherDiagnosticAxis0 : FisherDiagnosticPlane :=
  EuclideanSpace.single 0 1

noncomputable def fisherDiagnosticAxis1 : FisherDiagnosticPlane :=
  EuclideanSpace.single 1 1

theorem fisherDiagnosticAxes_orthogonal :
    ⟪fisherDiagnosticAxis1, fisherDiagnosticAxis0⟫_ℝ = 0 := by
  rw [fisherDiagnosticAxis1, fisherDiagnosticAxis0,
    EuclideanSpace.inner_single_left]
  simp

theorem fisherProjection_parallel_positiveFixture :
    fisherProjectionCoefficient
        (identityAdapterMetric : AdapterMetric FisherDiagnosticPlane)
        fisherDiagnosticAxis0 fisherDiagnosticAxis0 = 1 ∧
      fisherOrthogonalResidual
        (identityAdapterMetric : AdapterMetric FisherDiagnosticPlane)
        fisherDiagnosticAxis0 fisherDiagnosticAxis0 = 0 := by
  constructor
  · simp [fisherProjectionCoefficient, fisherDiagnosticAxis0]
  · apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [fisherOrthogonalResidual, fisherProjectionCoefficient,
        fisherDiagnosticAxis0]

/-- Euclidean distinctness can be entirely Fisher-orthogonal: this update has
zero natural component and spends its whole KL budget in the residual. -/
theorem fisherProjection_orthogonal_negativeFixture :
    fisherProjectionCoefficient
        (identityAdapterMetric : AdapterMetric FisherDiagnosticPlane)
        fisherDiagnosticAxis1 fisherDiagnosticAxis0 = 0 ∧
      fisherOrthogonalResidual
        (identityAdapterMetric : AdapterMetric FisherDiagnosticPlane)
        fisherDiagnosticAxis1 fisherDiagnosticAxis0 = fisherDiagnosticAxis1 ∧
      fisherKLBudget
        (identityAdapterMetric : AdapterMetric FisherDiagnosticPlane)
        fisherDiagnosticAxis1 = 1 / 2 := by
  have hprojection : fisherProjectionCoefficient
      (identityAdapterMetric : AdapterMetric FisherDiagnosticPlane)
      fisherDiagnosticAxis1 fisherDiagnosticAxis0 = 0 := by
    simp [fisherProjectionCoefficient, fisherDiagnosticAxes_orthogonal]
  constructor
  · exact hprojection
  constructor
  · rw [fisherOrthogonalResidual, hprojection, zero_smul, sub_zero]
  · simp [fisherKLBudget, fisherDiagnosticAxis1]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
