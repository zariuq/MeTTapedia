import Mathlib.Tactic

/-!
# Gradient-projection memory

Saha, Garg, and Roy (2021), *Gradient Projection Memory for Continual
Learning*, store orthonormal bases for activation subspaces learned by earlier
tasks.  Their fully connected update (Equation (6)) removes the right-hand
component `G M Mᵀ`; their convolutional update (Equation (7)) removes the
left-hand component `M Mᵀ G`; and their representation update (Equation (8))
applies the same left projector before extracting new singular vectors.

This file isolates that common projector algebra.  Orthonormal columns make
`M Mᵀ` an orthogonal projector, so every projected update is exactly
orthogonal to the stored basis.  Adding an orthogonal projector is equivalent
to another residual-projection pass, which captures the growing constrained
gradient space described by the source.

The boundary results are equally important.  A zero stored basis leaves the
gradient unchanged, a full basis removes all plasticity, and a concrete
nonorthonormal basis makes both idempotence and orthogonality fail.  Thus the
SVD/orthonormalization condition is a load-bearing hypothesis rather than an
implementation detail.  These are first-order gradient identities; finite
nonlinear retention still requires a separate curvature or fixed-Jacobian
certificate.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace GradientProjectionMemory

noncomputable section

variable {Coordinate Basis Output Sample : Type*}
  [Fintype Coordinate] [Fintype Basis]
  [DecidableEq Coordinate] [DecidableEq Basis]

/-- The stored activation subspace represented by the columns of `memory`. -/
def projector
    (memory : Matrix Coordinate Basis ℝ) :
    Matrix Coordinate Coordinate ℝ :=
  memory * memory.transpose

/-- The complementary operator used to remove stored-subspace components. -/
def residualProjector
    (memory : Matrix Coordinate Basis ℝ) :
    Matrix Coordinate Coordinate ℝ :=
  1 - projector memory

/-- The source's SVD construction supplies columns satisfying this identity. -/
def HasOrthonormalColumns
    (memory : Matrix Coordinate Basis ℝ) : Prop :=
  memory.transpose * memory = 1

/-- Equation (6): a fully connected gradient is projected on its input side. -/
def fullyConnectedUpdate
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Matrix Output Coordinate ℝ) :
    Matrix Output Coordinate ℝ :=
  gradient - gradient * projector memory

/-- Equation (7): a convolutional gradient is projected on its patch side. -/
def convolutionalUpdate
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Matrix Coordinate Output ℝ) :
    Matrix Coordinate Output ℝ :=
  gradient - projector memory * gradient

/-- Equation (8): discard representation components already stored in GPM. -/
def representationResidual
    (memory : Matrix Coordinate Basis ℝ)
    (representation : Matrix Coordinate Sample ℝ) :
    Matrix Coordinate Sample ℝ :=
  representation - projector memory * representation

omit [Fintype Coordinate] [DecidableEq Coordinate]
    [DecidableEq Basis] in
/-- The stored-subspace projector is symmetric independently of
orthonormality. -/
@[simp] theorem projector_transpose
    (memory : Matrix Coordinate Basis ℝ) :
    (projector memory).transpose = projector memory := by
  simp [projector, Matrix.transpose_mul]

omit [DecidableEq Coordinate] in
/-- Orthonormal columns make `M Mᵀ` idempotent. -/
theorem projector_idempotent
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory) :
    projector memory * projector memory = projector memory := by
  unfold projector
  calc
    (memory * memory.transpose) * (memory * memory.transpose) =
        memory * (memory.transpose * memory) * memory.transpose := by
      simp only [Matrix.mul_assoc]
    _ = memory * memory.transpose := by
      rw [orthonormal]
      simp

/-- The complementary projector is idempotent as well. -/
theorem residualProjector_idempotent
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory) :
    residualProjector memory * residualProjector memory =
      residualProjector memory := by
  have storedIdempotent :=
    projector_idempotent memory orthonormal
  unfold residualProjector
  calc
    (1 - projector memory) * (1 - projector memory) =
        1 - projector memory - projector memory +
          projector memory * projector memory := by
      noncomm_ring
    _ = 1 - projector memory := by
      rw [storedIdempotent]
      module

omit [DecidableEq Basis] in
/-- Equation (6) is equivalently right multiplication by the complementary
projector. -/
theorem fullyConnectedUpdate_eq_mul_residualProjector
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Matrix Output Coordinate ℝ) :
    fullyConnectedUpdate memory gradient =
      gradient * residualProjector memory := by
  simp [fullyConnectedUpdate, residualProjector, Matrix.mul_sub]

omit [DecidableEq Basis] in
/-- Equation (7) is equivalently left multiplication by the complementary
projector. -/
theorem convolutionalUpdate_eq_residualProjector_mul
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Matrix Coordinate Output ℝ) :
    convolutionalUpdate memory gradient =
      residualProjector memory * gradient := by
  simp [convolutionalUpdate, residualProjector, Matrix.sub_mul]

omit [DecidableEq Coordinate] in
/-- Fully connected projected gradients annihilate every stored basis
direction exactly. -/
theorem fullyConnectedUpdate_annihilates_basis
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Matrix Output Coordinate ℝ) :
    fullyConnectedUpdate memory gradient * memory = 0 := by
  unfold HasOrthonormalColumns at orthonormal
  simp [fullyConnectedUpdate, projector, Matrix.sub_mul,
    Matrix.mul_assoc, orthonormal]

omit [DecidableEq Coordinate] in
/-- Convolutional projected gradients are orthogonal to every stored patch
basis direction exactly. -/
theorem convolutionalUpdate_annihilates_basis
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Matrix Coordinate Output ℝ) :
    memory.transpose * convolutionalUpdate memory gradient = 0 := by
  unfold HasOrthonormalColumns at orthonormal
  simp [convolutionalUpdate, projector, Matrix.mul_sub,
    ← Matrix.mul_assoc, orthonormal]

omit [DecidableEq Coordinate] in
/-- Equation (8) removes every component in the existing representation
basis before the source's next SVD is taken. -/
theorem representationResidual_annihilates_basis
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (representation : Matrix Coordinate Sample ℝ) :
    memory.transpose * representationResidual memory representation = 0 := by
  unfold HasOrthonormalColumns at orthonormal
  simp [representationResidual, projector, Matrix.mul_sub,
    ← Matrix.mul_assoc, orthonormal]

/-! ## Growing the constrained gradient space -/

/-- Two idempotent projectors with mutually annihilating ranges combine into
another idempotent projector. -/
theorem add_orthogonal_projectors_idempotent
    (first second : Matrix Coordinate Coordinate ℝ)
    (firstIdempotent : first * first = first)
    (secondIdempotent : second * second = second)
    (firstThenSecond : first * second = 0)
    (secondThenFirst : second * first = 0) :
    (first + second) * (first + second) = first + second := by
  calc
    (first + second) * (first + second) =
        first * first + first * second +
          (second * first + second * second) := by
      noncomm_ring
    _ = first + second := by
      rw [firstIdempotent, secondIdempotent, firstThenSecond,
        secondThenFirst]
      simp

omit [DecidableEq Coordinate] in
/-- Residual projection by a newly added orthogonal subspace is exactly the
same as projection by the combined old-plus-new memory. -/
theorem sequential_leftResidual_eq_combined
    (first second : Matrix Coordinate Coordinate ℝ)
    (representation : Matrix Coordinate Sample ℝ)
    (secondAnnihilatesFirst : second * first = 0) :
    (representation - first * representation) -
        second * (representation - first * representation) =
      representation - (first + second) * representation := by
  simp [Matrix.mul_sub, Matrix.add_mul, ← Matrix.mul_assoc,
    secondAnnihilatesFirst]
  module

/-! ## Recovery, exhaustion, and executable boundaries -/

omit [DecidableEq Coordinate] [DecidableEq Basis] in
@[simp] theorem fullyConnectedUpdate_zeroMemory
    (gradient : Matrix Output Coordinate ℝ) :
    fullyConnectedUpdate
        (0 : Matrix Coordinate Basis ℝ) gradient =
      gradient := by
  simp [fullyConnectedUpdate, projector]

omit [DecidableEq Coordinate] [DecidableEq Basis] in
@[simp] theorem convolutionalUpdate_zeroMemory
    (gradient : Matrix Coordinate Output ℝ) :
    convolutionalUpdate
        (0 : Matrix Coordinate Basis ℝ) gradient =
      gradient := by
  simp [convolutionalUpdate, projector]

omit [DecidableEq Coordinate] [DecidableEq Basis] in
@[simp] theorem representationResidual_zeroMemory
    (representation : Matrix Coordinate Sample ℝ) :
    representationResidual
        (0 : Matrix Coordinate Basis ℝ) representation =
      representation := by
  simp [representationResidual, projector]

/-- If stored directions span the entire coordinate space, GPM has no
remaining fully connected plasticity. -/
@[simp] theorem fullyConnectedUpdate_fullMemory
    (gradient : Matrix Output Coordinate ℝ) :
    fullyConnectedUpdate
        (1 : Matrix Coordinate Coordinate ℝ) gradient =
      0 := by
  simp [fullyConnectedUpdate, projector]

/-- The same full-memory boundary removes every convolutional update. -/
@[simp] theorem convolutionalUpdate_fullMemory
    (gradient : Matrix Coordinate Output ℝ) :
    convolutionalUpdate
        (1 : Matrix Coordinate Coordinate ℝ) gradient =
      0 := by
  simp [convolutionalUpdate, projector]

abbrev TwoCoordinates := Fin 2
abbrev OneBasis := Fin 1

/-- One stored unit basis vector selecting the first coordinate. -/
def firstAxisMemory : Matrix TwoCoordinates OneBasis ℝ :=
  fun coordinate _ => if coordinate = 0 then 1 else 0

/-- A row gradient with a protected first component and a free second one. -/
def twoCoordinateGradient : Matrix OneBasis TwoCoordinates ℝ :=
  fun _ coordinate => if coordinate = 0 then 3 else 5

theorem firstAxisMemory_hasOrthonormalColumns :
    HasOrthonormalColumns firstAxisMemory := by
  ext row column
  fin_cases row
  fin_cases column
  norm_num [HasOrthonormalColumns, firstAxisMemory, Matrix.mul_apply]

/-- A partial memory removes the protected component and preserves the
orthogonal component. -/
theorem firstAxis_projection :
    fullyConnectedUpdate firstAxisMemory twoCoordinateGradient 0 0 = 0 ∧
      fullyConnectedUpdate firstAxisMemory
          twoCoordinateGradient 0 1 = 5 := by
  constructor <;>
    norm_num [fullyConnectedUpdate, projector, firstAxisMemory,
      twoCoordinateGradient, Matrix.mul_apply]

def scalarBasisMemory (scale : ℝ) :
    Matrix OneBasis OneBasis ℝ :=
  fun _ _ => scale

def scalarRepresentation (value : ℝ) :
    Matrix OneBasis OneBasis ℝ :=
  fun _ _ => value

/-- Without orthonormalization, `M Mᵀ` need not be a projector. -/
theorem nonorthonormal_memory_breaks_idempotence :
    let memory := scalarBasisMemory 2
    projector memory * projector memory ≠ projector memory := by
  intro memory idempotent
  have entry := congrFun (congrFun idempotent 0) 0
  norm_num [memory, scalarBasisMemory, projector, Matrix.mul_apply] at entry

/-- The same malformed memory fails to remove its own stored direction. -/
theorem nonorthonormal_memory_breaks_orthogonality :
    let memory := scalarBasisMemory 2
    let representation := scalarRepresentation 1
    memory.transpose *
        representationResidual memory representation ≠ 0 := by
  intro memory representation orthogonal
  have entry := congrFun (congrFun orthogonal 0) 0
  norm_num [memory, representation, scalarBasisMemory,
    scalarRepresentation, representationResidual, projector,
    Matrix.mul_apply] at entry

#print axioms projector_idempotent
#print axioms residualProjector_idempotent
#print axioms fullyConnectedUpdate_annihilates_basis
#print axioms convolutionalUpdate_annihilates_basis
#print axioms representationResidual_annihilates_basis
#print axioms add_orthogonal_projectors_idempotent
#print axioms sequential_leftResidual_eq_combined
#print axioms firstAxis_projection
#print axioms nonorthonormal_memory_breaks_idempotence
#print axioms nonorthonormal_memory_breaks_orthogonality

end

end GradientProjectionMemory

end Mettapedia.MachineLearning.ContinualLearning
