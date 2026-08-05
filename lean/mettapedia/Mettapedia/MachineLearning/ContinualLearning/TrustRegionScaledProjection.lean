import Mettapedia.MachineLearning.ContinualLearning.GradientProjectionMemory

/-!
# Task-specific scaled weight projections

Lin, Yang, Fan, and Zhang, *TRGP: Trust Region Gradient Projection for
Continual Learning* (arXiv:2202.02931), equations (1), (4)--(6), and (9),
combine two distinct mechanisms:

* the shared weight is updated through the residual projector of old-task
  activation memory, preserving its action on every stored basis direction;
* a new task receives a task-specific view of the frozen stored-subspace
  weight through a small coordinate scaling matrix.

This file isolates that finite matrix algebra.  Orthonormal stored columns
make the task-specific view act on stored coordinates exactly by the declared
scaling matrix, while leaving inputs orthogonal to the stored basis unchanged.
Identity scaling recovers the shared weight exactly.  A concrete fixture shows
that nonidentity scaling changes the new-task view without changing the shared
weight, and a nonorthonormal fixture shows that the coordinate-action theorem
fails without the source's SVD hypothesis.

These are exact single-layer linear identities.  They do not establish that
the source's projected-gradient norm is a reliable task-correlation measure,
that its top-K trust-region selection is stable, or that a nonlinear network
retains all old-task predictions after a finite training trajectory.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace TrustRegionScaledProjection

open GradientProjectionMemory

noncomputable section

variable {Coordinate Basis Output : Type*}
  [Fintype Coordinate] [Fintype Basis]
  [DecidableEq Basis]

/-- Equation (6): the frozen stored-subspace weight with its basis
coordinates transformed by the task-specific scaling matrix. -/
def scaledWeightProjection
    (weight : Matrix Output Coordinate ℝ)
    (memory : Matrix Coordinate Basis ℝ)
    (scale : Matrix Basis Basis ℝ) :
    Matrix Output Coordinate ℝ :=
  weight * memory * scale * memory.transpose

/-- Equation (9) for one trusted old-task subspace: replace the ordinary
stored-subspace projection by its task-specific scaled view. -/
def effectiveWeight
    (weight : Matrix Output Coordinate ℝ)
    (memory : Matrix Coordinate Basis ℝ)
    (scale : Matrix Basis Basis ℝ) :
    Matrix Output Coordinate ℝ :=
  weight +
    (scaledWeightProjection weight memory scale -
      weight * projector memory)

/-- Identity coordinate scaling recovers the shared weight exactly, without
requiring an orthonormality premise. -/
@[simp] theorem effectiveWeight_identityScale
    (weight : Matrix Output Coordinate ℝ)
    (memory : Matrix Coordinate Basis ℝ) :
    effectiveWeight weight memory 1 = weight := by
  simp [effectiveWeight, scaledWeightProjection, projector,
    Matrix.mul_assoc]

/-- Orthonormal stored columns make the scaled view act on stored basis
coordinates exactly through the declared small scaling matrix. -/
theorem effectiveWeight_mul_memory
    (weight : Matrix Output Coordinate ℝ)
    (memory : Matrix Coordinate Basis ℝ)
    (scale : Matrix Basis Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory) :
    effectiveWeight weight memory scale * memory =
      weight * memory * scale := by
  unfold effectiveWeight scaledWeightProjection projector
  unfold HasOrthonormalColumns at orthonormal
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc,
    orthonormal, Matrix.mul_one]
  module

/-- Coordinate form of `effectiveWeight_mul_memory`: a stored-subspace input
`memory * coordinates` is evaluated by scaling its coordinates first. -/
theorem effectiveWeight_mulVec_storedCoordinates
    (weight : Matrix Output Coordinate ℝ)
    (memory : Matrix Coordinate Basis ℝ)
    (scale : Matrix Basis Basis ℝ)
    (coordinates : Basis → ℝ)
    (orthonormal : HasOrthonormalColumns memory) :
    (effectiveWeight weight memory scale).mulVec
        (memory.mulVec coordinates) =
      (weight * memory * scale).mulVec coordinates := by
  rw [Matrix.mulVec_mulVec, effectiveWeight_mul_memory
    weight memory scale orthonormal]

omit [DecidableEq Basis] in
/-- Inputs orthogonal to the stored basis do not see the task-specific
correction. -/
theorem effectiveWeight_mulVec_eq_weight_of_orthogonal
    (weight : Matrix Output Coordinate ℝ)
    (memory : Matrix Coordinate Basis ℝ)
    (scale : Matrix Basis Basis ℝ)
    (input : Coordinate → ℝ)
    (orthogonal : memory.transpose.mulVec input = 0) :
    (effectiveWeight weight memory scale).mulVec input =
      weight.mulVec input := by
  have scaledZero :
      (scaledWeightProjection weight memory scale).mulVec input = 0 := by
    unfold scaledWeightProjection
    rw [← Matrix.mulVec_mulVec, orthogonal]
    simp
  have projectionZero :
      (weight * projector memory).mulVec input = 0 := by
    unfold projector
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, orthogonal]
    simp
  rw [effectiveWeight, Matrix.add_mulVec, Matrix.sub_mulVec,
    scaledZero, projectionZero]
  simp

/-- Equations (1) and (4): an arbitrary residual-projected shared-weight
update preserves the old weight action on every stored basis direction. -/
theorem add_projectedUpdate_mul_memory
    (weight : Matrix Output Coordinate ℝ)
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Matrix Output Coordinate ℝ)
    (stepSize : ℝ)
    (orthonormal : HasOrthonormalColumns memory) :
    (weight + stepSize • fullyConnectedUpdate memory gradient) * memory =
      weight * memory := by
  rw [Matrix.add_mul, Matrix.smul_mul,
    fullyConnectedUpdate_annihilates_basis
      memory orthonormal gradient]
  simp

/-- Consequently the ordinary frozen stored-subspace projection is unchanged
by a residual-projected shared-weight update. -/
theorem projector_weight_preserved_after_projectedUpdate
    (weight : Matrix Output Coordinate ℝ)
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Matrix Output Coordinate ℝ)
    (stepSize : ℝ)
    (orthonormal : HasOrthonormalColumns memory) :
    (weight + stepSize • fullyConnectedUpdate memory gradient) *
        projector memory =
      weight * projector memory := by
  unfold projector
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    add_projectedUpdate_mul_memory
      weight memory gradient stepSize orthonormal]

/-! ## Exact positive and negative fixtures -/

abbrev TwoCoordinates := Fin 2
abbrev OneBasis := Fin 1

def firstAxisMemory : Matrix TwoCoordinates OneBasis ℝ :=
  fun coordinate _ => if coordinate = 0 then 1 else 0

def exampleWeight : Matrix Unit TwoCoordinates ℝ :=
  fun _ coordinate => if coordinate = 0 then 2 else 3

def fourfoldScale : Matrix OneBasis OneBasis ℝ :=
  fun _ _ => 4

def firstAxisInput : TwoCoordinates → ℝ :=
  fun coordinate => if coordinate = 0 then 1 else 0

def secondAxisInput : TwoCoordinates → ℝ :=
  fun coordinate => if coordinate = 1 then 1 else 0

theorem firstAxisMemory_orthonormal :
    HasOrthonormalColumns firstAxisMemory := by
  ext row column
  fin_cases row
  fin_cases column
  norm_num [HasOrthonormalColumns, firstAxisMemory, Matrix.mul_apply]

/-- Nonidentity task-specific scaling changes the trusted old-subspace view
from two to eight while leaving the orthogonal coordinate at three. -/
theorem fourfoldScale_changes_first_preserves_second :
    (effectiveWeight exampleWeight firstAxisMemory fourfoldScale).mulVec
        firstAxisInput = (fun _ => 8) ∧
      (effectiveWeight exampleWeight firstAxisMemory fourfoldScale).mulVec
        secondAxisInput = (fun _ => 3) := by
  constructor <;>
    funext output <;>
    cases output <;>
    norm_num [effectiveWeight, scaledWeightProjection, projector,
      exampleWeight, firstAxisMemory, fourfoldScale,
      firstAxisInput, secondAxisInput, Matrix.mulVec,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The task-specific view may change even though the shared weight object is
untouched; it must therefore remain task-indexed rather than overwrite the
old-task model. -/
theorem fourfoldScale_view_separates_from_shared :
    effectiveWeight exampleWeight firstAxisMemory fourfoldScale ≠
      exampleWeight := by
  intro equalWeights
  have firstEntry := congrFun (congrFun equalWeights ()) 0
  norm_num [effectiveWeight, scaledWeightProjection, projector,
    exampleWeight, firstAxisMemory, fourfoldScale,
    Matrix.mul_apply, Fin.sum_univ_two] at firstEntry

/-- Without orthonormal columns, the nominal scaling matrix does not act as
the declared coordinate transform on stored-subspace inputs. -/
theorem nonorthonormal_memory_breaks_scaledCoordinate_action :
    let memory : Matrix Unit Unit ℝ := fun _ _ => 2
    let weight : Matrix Unit Unit ℝ := fun _ _ => 1
    let scale : Matrix Unit Unit ℝ := fun _ _ => 2
    let coordinates : Unit → ℝ := fun _ => 1
    (effectiveWeight weight memory scale).mulVec
        (memory.mulVec coordinates) ≠
      (weight * memory * scale).mulVec coordinates := by
  dsimp
  intro equality
  have entry := congrFun equality ()
  norm_num [effectiveWeight, scaledWeightProjection, projector,
    Matrix.mulVec, Matrix.mul_apply] at entry

#print axioms effectiveWeight_identityScale
#print axioms effectiveWeight_mul_memory
#print axioms effectiveWeight_mulVec_storedCoordinates
#print axioms effectiveWeight_mulVec_eq_weight_of_orthogonal
#print axioms add_projectedUpdate_mul_memory
#print axioms projector_weight_preserved_after_projectedUpdate
#print axioms fourfoldScale_changes_first_preserves_second
#print axioms fourfoldScale_view_separates_from_shared
#print axioms nonorthonormal_memory_breaks_scaledCoordinate_action

end

end TrustRegionScaledProjection

end Mettapedia.MachineLearning.ContinualLearning
