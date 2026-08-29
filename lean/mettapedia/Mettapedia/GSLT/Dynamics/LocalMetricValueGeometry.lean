import Mettapedia.GSLT.Dynamics.TypedValueGeometry
import Mettapedia.PLN.TruthValues.PLNInformationGeometry
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-!
# Local metric geometry for typed value channels

`ValueGeometry` describes a global distance or directed effort on values.  A
statistical or spacetime-like manifold additionally needs a local bilinear
form on tangent directions and an explicit law for changing coordinates.

This module supplies that second layer without privileging it in every value:

* `LocalMetricField` is a point-indexed real bilinear form;
* positive definiteness is an optional property, so Fisher and indefinite
  geometries do not need to share a false common signature;
* `MetricMap` carries both a point map and its tangent transport and proves
  preservation of the local tensor;
* identity and composition make such transports reusable between cognitive
  representations;
* the Bernoulli Fisher tensor is a genuine positive-definite instance, and
  the existing mean/log-odds pullback theorem becomes a `MetricMap`;
* a four-coordinate diagonal tensor exhibits one negative and three positive
  coordinate directions.  It is an indefinite metric example, not a claim to
  implement general relativity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.LocalMetricValueGeometry

open Mettapedia.GSLT.Dynamics.TypedValueGeometry
open Mettapedia.PLN.TruthValues.PLNInformationGeometry
open scoped BigOperators

universe uPoint uTangent uTargetPoint uTargetTangent

/-! ## Local tensor fields and coordinate transport -/

/-- A symmetric local bilinear form on a uniform tangent carrier.  Positivity
and nondegeneracy are separate predicates because many useful control
geometries are directed or indefinite. -/
structure LocalMetricField (Point : Type uPoint) (Tangent : Type uTangent)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  tensor : Point → LinearMap.BilinForm ℝ Tangent
  symmetric : ∀ point first second,
    tensor point first second = tensor point second first

namespace LocalMetricField

variable {Point : Type uPoint} {Tangent : Type uTangent}
  [AddCommGroup Tangent] [Module ℝ Tangent]

/-- Positive definiteness is meaningful for statistical and Riemannian
metrics, but is deliberately not part of `LocalMetricField`. -/
def PositiveDefinite (field : LocalMetricField Point Tangent) : Prop :=
  ∀ point tangent, tangent ≠ 0 → 0 < field.tensor point tangent tangent

end LocalMetricField

/-- A coordinate change includes the tangent transport and the commuting
metric square.  A point map alone is not enough to compare local tensors. -/
structure MetricMap
    {SourcePoint : Type uPoint} {SourceTangent : Type uTangent}
    {TargetPoint : Type uTargetPoint} {TargetTangent : Type uTargetTangent}
    [AddCommGroup SourceTangent] [Module ℝ SourceTangent]
    [AddCommGroup TargetTangent] [Module ℝ TargetTangent]
    (source : LocalMetricField SourcePoint SourceTangent)
    (target : LocalMetricField TargetPoint TargetTangent) where
  point : SourcePoint → TargetPoint
  tangent : ∀ _sourcePoint, SourceTangent →ₗ[ℝ] TargetTangent
  preserves : ∀ sourcePoint first second,
    target.tensor (point sourcePoint)
        (tangent sourcePoint first) (tangent sourcePoint second) =
      source.tensor sourcePoint first second

namespace MetricMap

/-- Identity coordinates preserve every local metric field. -/
def identity
    {Point : Type uPoint} {Tangent : Type uTangent}
    [AddCommGroup Tangent] [Module ℝ Tangent]
    (field : LocalMetricField Point Tangent) : MetricMap field field where
  point := id
  tangent := fun _ => LinearMap.id
  preserves := by
    intro point first second
    rfl

/-- Metric-preserving coordinate changes compose, including their tangent
maps at the correct intermediate point. -/
def comp
    {FirstPoint : Type uPoint} {FirstTangent : Type uTangent}
    {SecondPoint : Type uTargetPoint} {SecondTangent : Type uTargetTangent}
    {ThirdPoint : Type*} {ThirdTangent : Type*}
    [AddCommGroup FirstTangent] [Module ℝ FirstTangent]
    [AddCommGroup SecondTangent] [Module ℝ SecondTangent]
    [AddCommGroup ThirdTangent] [Module ℝ ThirdTangent]
    {firstField : LocalMetricField FirstPoint FirstTangent}
    {secondField : LocalMetricField SecondPoint SecondTangent}
    {thirdField : LocalMetricField ThirdPoint ThirdTangent}
    (first : MetricMap firstField secondField)
    (second : MetricMap secondField thirdField) :
    MetricMap firstField thirdField where
  point := second.point ∘ first.point
  tangent := fun point =>
    (second.tangent (first.point point)).comp (first.tangent point)
  preserves := by
    intro point left right
    change thirdField.tensor (second.point (first.point point))
        (second.tangent (first.point point) (first.tangent point left))
        (second.tangent (first.point point) (first.tangent point right)) = _
    rw [second.preserves, first.preserves]

end MetricMap

/-! ## Bernoulli Fisher geometry -/

/-- Points of the open Bernoulli simplex. -/
abbrev OpenBernoulli := Set.Ioo (0 : ℝ) 1

/-- The Bernoulli Fisher tensor bundled as a bilinear form. -/
noncomputable def bernoulliFisherBilinear (point : OpenBernoulli) :
    LinearMap.BilinForm ℝ ℝ :=
  LinearMap.mk₂ ℝ
    (fun first second => bernoulliFisherTensor point.1 first second)
    (by
      intro first second third
      unfold bernoulliFisherTensor
      ring)
    (by
      intro scalar first second
      unfold bernoulliFisherTensor
      ring)
    (by
      intro first second third
      unfold bernoulliFisherTensor
      ring)
    (by
      intro scalar first second
      unfold bernoulliFisherTensor
      ring)

/-- The open Bernoulli simplex with its genuine Fisher metric tensor. -/
noncomputable def bernoulliFisherField :
    LocalMetricField OpenBernoulli ℝ where
  tensor := bernoulliFisherBilinear
  symmetric := by
    intro point first second
    simp only [bernoulliFisherBilinear, LinearMap.mk₂_apply]
    exact bernoulliFisherTensor_symm point.1 first second

/-- The Bernoulli Fisher field is positive definite on the open simplex. -/
theorem bernoulliFisherField_positiveDefinite :
    bernoulliFisherField.PositiveDefinite := by
  intro point tangent nonzero
  simpa [bernoulliFisherField, bernoulliFisherBilinear] using
    (bernoulliFisherTensor_diag_pos point.2.1 point.2.2 nonzero)

/-- The natural/log-odds coordinate with its pulled-back Fisher tensor. -/
noncomputable def bernoulliNaturalFisherBilinear (theta : ℝ) :
    LinearMap.BilinForm ℝ ℝ :=
  LinearMap.mk₂ ℝ
    (fun first second => bernoulliNaturalFisherTensor theta first second)
    (by
      intro first second third
      unfold bernoulliNaturalFisherTensor
      ring)
    (by
      intro scalar first second
      unfold bernoulliNaturalFisherTensor
      ring)
    (by
      intro first second third
      unfold bernoulliNaturalFisherTensor
      ring)
    (by
      intro scalar first second
      unfold bernoulliNaturalFisherTensor
      ring)

noncomputable def bernoulliNaturalFisherField :
    LocalMetricField ℝ ℝ where
  tensor := bernoulliNaturalFisherBilinear
  symmetric := by
    intro theta first second
    simp only [bernoulliNaturalFisherBilinear, LinearMap.mk₂_apply]
    exact bernoulliNaturalFisherTensor_symm theta first second

/-- The logistic chart lands in the open Bernoulli simplex. -/
noncomputable def logisticOpenPoint (theta : ℝ) : OpenBernoulli :=
  ⟨bernoulliNaturalToMean theta,
    bernoulliNaturalToMean_pos theta,
    bernoulliNaturalToMean_lt_one theta⟩

/-- Differential of the logistic chart at one natural-coordinate point. -/
noncomputable def logisticTangent (theta : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun tangent :=
    bernoulliNaturalToMean theta *
      (1 - bernoulliNaturalToMean theta) * tangent
  map_add' := by
    intro first second
    ring
  map_smul' := by
    intro scalar tangent
    simp
    ring

/-- The existing Fisher pullback theorem is precisely a metric-preserving
map from log-odds coordinates to mean coordinates. -/
noncomputable def logisticFisherMetricMap :
    MetricMap bernoulliNaturalFisherField bernoulliFisherField where
  point := logisticOpenPoint
  tangent := logisticTangent
  preserves := by
    intro theta first second
    simp only [bernoulliFisherField, bernoulliFisherBilinear,
      bernoulliNaturalFisherField, bernoulliNaturalFisherBilinear,
      logisticOpenPoint, logisticTangent, LinearMap.mk₂_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    exact bernoulliFisherTensor_pullback_logOdds theta first second

/-! ## Global Hellinger geometry -/

/-- The Hellinger embedding also induces a genuine global pseudometric on the
same statistical values.  This is separate from the local Fisher tensor. -/
noncomputable def bernoulliHellingerGeometry : ValueGeometry OpenBernoulli :=
  (ValueGeometry.ofPseudoMetric (ℝ × ℝ)).comap
    (fun point => bernoulliHellingerEmbedding point.1)

theorem bernoulliHellingerGeometry_symmetric :
    bernoulliHellingerGeometry.Symmetric := by
  intro first second
  exact dist_comm _ _

/-! ## A four-coordinate indefinite tensor -/

abbrev Vector4 := Fin 4 → ℝ

/-- A diagonal four-coordinate tensor with one negative and three positive
directions.  It is a minimal indefinite-metric inhabitant for testing typed
tensor channels. -/
def oneTimeThreeSpaceTensor : Tensor4 :=
  fun row column =>
    if row = column then
      if row = 0 then -1 else 1
    else 0

/-- Evaluate a rank-two tensor on two coordinate vectors. -/
noncomputable def tensorPairing
    (tensor : Tensor4) (first second : Vector4) : ℝ :=
  ∑ row, ∑ column, tensor row column * first row * second column

def timeBasis : Vector4 :=
  fun coordinate => if coordinate = 0 then 1 else 0

def firstSpaceBasis : Vector4 :=
  fun coordinate => if coordinate = 1 then 1 else 0

/-- Positive and negative controls for the indefinite signature. -/
theorem oneTimeThreeSpace_signature_canary :
    tensorPairing oneTimeThreeSpaceTensor timeBasis timeBasis = -1 ∧
      tensorPairing oneTimeThreeSpaceTensor
        firstSpaceBasis firstSpaceBasis = 1 := by
  norm_num [tensorPairing, oneTimeThreeSpaceTensor, timeBasis,
    firstSpaceBasis, Fin.sum_univ_four]

/-! ## Axiom audit -/

#print axioms MetricMap.comp
#print axioms bernoulliFisherField_positiveDefinite
#print axioms logisticFisherMetricMap
#print axioms bernoulliHellingerGeometry_symmetric
#print axioms oneTimeThreeSpace_signature_canary

end Mettapedia.GSLT.Dynamics.LocalMetricValueGeometry
