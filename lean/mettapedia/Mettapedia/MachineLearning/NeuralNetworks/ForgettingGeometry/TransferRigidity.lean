import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.ElementaryHolonomy
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Coordinate transfer and its rigidity boundary

An invertible linear coordinate change conjugates curvature commutators, so
their characteristic polynomials are invariant.  This is the exact finite
linear content of transfer across a `C¹` chart at a point.

Euclidean symmetry and polar rotation are not invariants of arbitrary
similarity.  Orthogonal conjugation preserves symmetry, while an explicit
nonorthogonal shear sends a symmetric matrix to a nonsymmetric one.  A final
scalar quadratic germ shows that agreement of value and first derivative at
one point does not control the Hessian.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry

/-! ## Similarity invariants -/

/-- Matrix commutator in the order `first` then `second`. -/
noncomputable def matrixCommutator {Index : Type*} [Fintype Index]
    (first second : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  second * first - first * second

/-- Conjugation by an invertible linear coordinate map. -/
noncomputable def unitConjugate {Index : Type*} [Fintype Index]
    [DecidableEq Index]
    (coordinate : (Matrix Index Index ℝ)ˣ)
    (operator : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  (coordinate : Matrix Index Index ℝ) * operator *
    (↑coordinate⁻¹ : Matrix Index Index ℝ)

/-- Curvature commutators transform covariantly under every invertible linear
coordinate change. -/
theorem matrixCommutator_unitConjugate
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (coordinate : (Matrix Index Index ℝ)ˣ)
    (first second : Matrix Index Index ℝ) :
    matrixCommutator (unitConjugate coordinate first)
        (unitConjugate coordinate second) =
      unitConjugate coordinate (matrixCommutator first second) := by
  simp [matrixCommutator, unitConjugate, Matrix.mul_assoc,
    mul_sub, sub_mul]

/-- Consequently the full commutator characteristic polynomial, hence its
algebraic spectrum with multiplicities, is coordinate invariant. -/
theorem matrixCommutator_charpoly_unitConjugate
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (coordinate : (Matrix Index Index ℝ)ˣ)
    (first second : Matrix Index Index ℝ) :
    (matrixCommutator (unitConjugate coordinate first)
        (unitConjugate coordinate second)).charpoly =
      (matrixCommutator first second).charpoly := by
  rw [matrixCommutator_unitConjugate]
  unfold unitConjugate
  rw [Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj coordinate (matrixCommutator first second)

/-! ## Orthogonal versus unrestricted coordinate changes -/

/-- Euclidean metric transport by an orthogonal coordinate matrix. -/
noncomputable def orthogonalConjugate {Index : Type*} [Fintype Index]
    (coordinate operator : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  coordinate * operator * coordinate.transpose

/-- Orthogonal conjugation preserves the elementary zero-rotation criterion.
Only the transpose form of the coordinate inverse is needed for this
direction. -/
theorem orthogonalConjugate_trivialRotationProxy
    {Index : Type*} [Fintype Index]
    (coordinate operator : Matrix Index Index ℝ)
    (hoperator : TrivialRotationProxy operator) :
    TrivialRotationProxy (orthogonalConjugate coordinate operator) := by
  unfold TrivialRotationProxy orthogonalConjugate Matrix.IsSymm at *
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hoperator]
  simp [Matrix.mul_assoc]

/-- A concrete nonorthogonal shear unit. -/
noncomputable def shearCoordinateUnit :
    (Matrix (Fin 2) (Fin 2) ℝ)ˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Symmetric operator used to test unrestricted similarity. -/
noncomputable def shearSymmetricOperator : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 2]

theorem shearSymmetricOperator_isSymm : shearSymmetricOperator.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [shearSymmetricOperator]

/-- Negative fixture: unrestricted similarity does not preserve Euclidean
symmetry.  Therefore Euclidean polar angles cannot be transported through a
general nonorthogonal `C¹` coordinate map without also transporting the
metric. -/
theorem nonorthogonalSimilarity_not_preserve_trivialRotationProxy_negativeExample :
    TrivialRotationProxy shearSymmetricOperator ∧
      ¬ TrivialRotationProxy
        (unitConjugate shearCoordinateUnit shearSymmetricOperator) := by
  constructor
  · exact shearSymmetricOperator_isSymm
  · intro hsymm
    have h01 := hsymm.apply 0 1
    norm_num [unitConjugate, shearCoordinateUnit, shearSymmetricOperator,
      Matrix.mul_apply, Fin.sum_univ_two] at h01

/-! ## Pointwise first-order agreement does not determine curvature -/

/-- Coefficient presentation of a scalar quadratic germ. -/
structure ScalarQuadraticGerm where
  value : ℝ
  linear : ℝ
  curvature : ℝ

/-- Evaluation of the quadratic germ around the distinguished point zero. -/
noncomputable def ScalarQuadraticGerm.evaluate
    (germ : ScalarQuadraticGerm) (offset : ℝ) : ℝ :=
  germ.value + germ.linear * offset + germ.curvature * offset ^ 2 / 2

/-- First derivative of the represented scalar quadratic. -/
noncomputable def ScalarQuadraticGerm.gradient
    (germ : ScalarQuadraticGerm) (offset : ℝ) : ℝ :=
  germ.linear + germ.curvature * offset

noncomputable def flatQuadraticGerm : ScalarQuadraticGerm :=
  ⟨0, 0, 0⟩

noncomputable def curvedQuadraticGerm : ScalarQuadraticGerm :=
  ⟨0, 0, 1⟩

/-- Negative fixture: two quadratics can agree in output and first derivative
at the transfer point while their Hessians differ by one.  Pointwise `C⁰`
matching, even supplemented by one matching first jet, is therefore
insufficient for curvature transport. -/
theorem pointwiseAgreement_not_determineHessian_negativeExample :
    flatQuadraticGerm.evaluate 0 = curvedQuadraticGerm.evaluate 0 ∧
      flatQuadraticGerm.gradient 0 = curvedQuadraticGerm.gradient 0 ∧
      |flatQuadraticGerm.curvature - curvedQuadraticGerm.curvature| = 1 := by
  norm_num [ScalarQuadraticGerm.evaluate, ScalarQuadraticGerm.gradient,
    flatQuadraticGerm, curvedQuadraticGerm]

#print axioms matrixCommutator_unitConjugate
#print axioms matrixCommutator_charpoly_unitConjugate
#print axioms orthogonalConjugate_trivialRotationProxy
#print axioms nonorthogonalSimilarity_not_preserve_trivialRotationProxy_negativeExample
#print axioms pointwiseAgreement_not_determineHessian_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
