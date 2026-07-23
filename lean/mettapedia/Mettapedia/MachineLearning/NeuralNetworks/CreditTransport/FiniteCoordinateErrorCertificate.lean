import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionEvaluationError
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteMatrixOperatorBounds

/-!
# Finite coordinatewise evaluation-error certificates

An independently checked interval evaluation naturally supplies one error
radius per output coordinate.  The credit-transport layer instead consumes a
single Euclidean local-error radius.  This file gives the conservative bridge:
the Euclidean mismatch is bounded by the sum of the nonnegative coordinate
radii, which then instantiates `LocalEvaluationErrorCertificate`.

No interval algorithm or floating-point model is assumed here.  The theorem
only checks the finite certificate after its coordinate bounds are supplied.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FiniteCoordinateErrorCertificate

noncomputable section

open scoped BigOperators
open FiniteMatrixOperatorBounds
open FinitePrecisionEvaluationError

variable {Index X : Type*}
  [Fintype Index] [DecidableEq Index]

/-- Coordinatewise absolute-error bounds between a runtime vector and an ideal
real vector. -/
structure CoordinatewiseMismatchCertificate
    (runtime ideal : EuclideanSpace ℝ Index)
    (coordinateRadius : Index → ℝ) : Prop where
  coordinateRadius_nonneg : ∀ index, 0 ≤ coordinateRadius index
  coordinate_mismatch_le : ∀ index,
    |runtime index - ideal index| ≤ coordinateRadius index

/-- Conservative scalar radius obtained by summing the coordinate radii. -/
def totalCoordinateRadius (coordinateRadius : Index → ℝ) : ℝ :=
  ∑ index, coordinateRadius index

omit [DecidableEq Index] in
theorem totalCoordinateRadius_nonneg
    {runtime ideal : EuclideanSpace ℝ Index}
    {coordinateRadius : Index → ℝ}
    (certificate : CoordinatewiseMismatchCertificate
      runtime ideal coordinateRadius) :
    0 ≤ totalCoordinateRadius coordinateRadius := by
  exact Finset.sum_nonneg fun index _ ↦
    certificate.coordinateRadius_nonneg index

/-- Coordinatewise bounds imply a Euclidean mismatch bound by the finite
entrywise one-norm. -/
theorem norm_sub_le_totalCoordinateRadius
    (runtime ideal : EuclideanSpace ℝ Index)
    (coordinateRadius : Index → ℝ)
    (certificate : CoordinatewiseMismatchCertificate
      runtime ideal coordinateRadius) :
    ‖runtime - ideal‖ ≤ totalCoordinateRadius coordinateRadius := by
  calc
    ‖runtime - ideal‖ ≤ ∑ index, |(runtime - ideal) index| :=
      euclidean_norm_le_entrywiseL1 _
    _ = ∑ index, |runtime index - ideal index| := rfl
    _ ≤ ∑ index, coordinateRadius index := by
      exact Finset.sum_le_sum fun index _ ↦
        certificate.coordinate_mismatch_le index
    _ = totalCoordinateRadius coordinateRadius := rfl

/-- A finite coordinatewise checker can discharge the local-error premise of
the compositional numerical transport theorem. -/
def CoordinatewiseMismatchCertificate.toLocalEvaluationErrorCertificate
    [NormedAddCommGroup X]
    (idealMap : X → EuclideanSpace ℝ Index)
    (runtimeInput : X) (runtimeOutput : EuclideanSpace ℝ Index)
    (coordinateRadius : Index → ℝ)
    (certificate : CoordinatewiseMismatchCertificate
      runtimeOutput (idealMap runtimeInput) coordinateRadius) :
    LocalEvaluationErrorCertificate idealMap runtimeInput runtimeOutput
      (totalCoordinateRadius coordinateRadius) where
  localError_nonneg := Finset.sum_nonneg fun index _ ↦
    certificate.coordinateRadius_nonneg index
  output_error_le := norm_sub_le_totalCoordinateRadius
    runtimeOutput (idealMap runtimeInput) coordinateRadius certificate

/-! ## Positive and negative fixtures -/

private def twoOnes : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun _ : Fin 2 ↦ (1 : ℝ)

private def unitCoordinateRadius : Fin 2 → ℝ := fun _ ↦ 1

private def twoOnesCertificate : CoordinatewiseMismatchCertificate
    twoOnes 0 unitCoordinateRadius where
  coordinateRadius_nonneg := by
    intro index
    norm_num [unitCoordinateRadius]
  coordinate_mismatch_le := by
    intro index
    norm_num [twoOnes, unitCoordinateRadius]

/-- The summed coordinate certificate safely bounds a two-dimensional
mismatch. -/
theorem twoOnes_mismatch_le_summed_radius :
    ‖twoOnes - 0‖ ≤ totalCoordinateRadius unitCoordinateRadius := by
  exact norm_sub_le_totalCoordinateRadius
    twoOnes 0 unitCoordinateRadius twoOnesCertificate

/-- The largest coordinate radius alone is not a Euclidean error bound: two
unit coordinate errors have Euclidean norm strictly larger than one. -/
theorem maximum_coordinate_radius_alone_fails :
    ¬ ‖twoOnes - 0‖ ≤ 1 := by
  intro hbound
  have hsquare :=
    (sq_le_sq₀ (norm_nonneg (twoOnes - 0)) (by norm_num)).2 hbound
  norm_num [twoOnes, EuclideanSpace.real_norm_sq_eq] at hsquare

#print axioms norm_sub_le_totalCoordinateRadius
#print axioms maximum_coordinate_radius_alone_fails

end

end FiniteCoordinateErrorCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
