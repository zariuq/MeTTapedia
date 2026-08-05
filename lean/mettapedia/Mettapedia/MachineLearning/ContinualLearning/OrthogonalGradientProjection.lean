import Mettapedia.MachineLearning.ContinualLearning.GradientProjectionMemory
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Multi-direction orthogonal gradient projection

Farajtabar et al., *Orthogonal Gradient Descent for Continual Learning*
(2020), Algorithm 1, Equation (9), and Lemma 3.1, subtract the projection of a
new-task gradient onto an orthogonal basis of stored model gradients.  The
remaining direction is orthogonal to every stored basis vector and its
negative remains a descent direction for the current loss.

This file recovers the multi-direction theorem in finite real coordinates.
With orthonormal stored columns, the residual update is annihilated by the
stored basis, decomposes the current gradient orthogonally, and satisfies the
exact identity

`⟪-residual, gradient⟫ = -‖residual‖²`.

The result is stronger and more informative than a weak descent inequality.
It also exposes two essential boundaries: a full stored basis leaves no
plasticity, and a nonorthonormal stored basis can turn the nominal
"projected" negative gradient into a strict ascent direction.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace OrthogonalGradientProjection

open GradientProjectionMemory

noncomputable section

variable {Coordinate Basis : Type*}
  [Fintype Coordinate] [Fintype Basis]
  [DecidableEq Coordinate] [DecidableEq Basis]

/-- Algorithm 1 / Equation (9): remove all components represented by the
stored gradient basis. -/
def projectedGradient
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Coordinate → ℝ) : Coordinate → ℝ :=
  (residualProjector memory).mulVec gradient

omit [DecidableEq Basis] in
/-- The residual-projector formula is the original gradient minus its stored
subspace component. -/
theorem projectedGradient_eq_sub_projector
    (memory : Matrix Coordinate Basis ℝ)
    (gradient : Coordinate → ℝ) :
    projectedGradient memory gradient =
      gradient - (projector memory).mulVec gradient := by
  simp [projectedGradient, residualProjector, Matrix.sub_mulVec]

/-- Orthonormal stored columns make the projected gradient exactly
orthogonal to every stored direction. -/
theorem transpose_mulVec_projectedGradient_eq_zero
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    memory.transpose.mulVec (projectedGradient memory gradient) = 0 := by
  have matrixZero :
      memory.transpose * residualProjector memory = 0 := by
    unfold residualProjector projector HasOrthonormalColumns at *
    calc
      memory.transpose * (1 - memory * memory.transpose) =
          memory.transpose -
            (memory.transpose * memory) * memory.transpose := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by
        rw [orthonormal]
        simp
  change memory.transpose.mulVec
      ((residualProjector memory).mulVec gradient) = 0
  rw [Matrix.mulVec_mulVec, matrixZero]
  simp

/-- The projected gradient is orthogonal to the component removed by the
stored projector. -/
theorem projectedGradient_dot_removed_eq_zero
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    projectedGradient memory gradient ⬝ᵥ
        (projector memory).mulVec gradient = 0 := by
  have vecMulEq :
      Matrix.vecMul (projectedGradient memory gradient) memory =
        memory.transpose.mulVec
          (projectedGradient memory gradient) := by
    simpa using
      (Matrix.vecMul_transpose memory.transpose
        (projectedGradient memory gradient))
  rw [projector, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, vecMulEq,
    transpose_mulVec_projectedGradient_eq_zero
      memory orthonormal gradient]
  simp

/-- Exact Pythagorean identity behind OGD's current-task descent claim. -/
theorem projectedGradient_dot_gradient_eq_self
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    projectedGradient memory gradient ⬝ᵥ gradient =
      projectedGradient memory gradient ⬝ᵥ
        projectedGradient memory gradient := by
  have decomposition :
      gradient =
        (projector memory).mulVec gradient +
          projectedGradient memory gradient := by
    rw [projectedGradient_eq_sub_projector]
    module
  calc
    projectedGradient memory gradient ⬝ᵥ gradient =
        projectedGradient memory gradient ⬝ᵥ
          ((projector memory).mulVec gradient +
            projectedGradient memory gradient) := by
      exact congrArg
        (fun right => projectedGradient memory gradient ⬝ᵥ right)
        decomposition
    _ = projectedGradient memory gradient ⬝ᵥ
          projectedGradient memory gradient := by
      rw [dotProduct_add,
        projectedGradient_dot_removed_eq_zero
          memory orthonormal gradient]
      simp

omit [Fintype Basis] [DecidableEq Coordinate] [DecidableEq Basis] in
/-- Squared Euclidean length is nonnegative in finite real coordinates. -/
theorem dotProduct_self_nonnegative_local
    (vector : Coordinate → ℝ) :
    0 ≤ vector ⬝ᵥ vector := by
  unfold dotProduct
  exact Finset.sum_nonneg (fun coordinate _ =>
    mul_self_nonneg (vector coordinate))

/-- Source Lemma 3.1, sharpened to equality: the negative projected gradient
has directional derivative exactly minus its squared Euclidean length. -/
theorem neg_projectedGradient_dot_gradient
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    (-projectedGradient memory gradient) ⬝ᵥ gradient =
      -(projectedGradient memory gradient ⬝ᵥ
          projectedGradient memory gradient) := by
  rw [neg_dotProduct,
    projectedGradient_dot_gradient_eq_self
      memory orthonormal gradient]

/-- The OGD direction is always a weak descent direction. -/
theorem neg_projectedGradient_dot_gradient_nonpos
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ) :
    (-projectedGradient memory gradient) ⬝ᵥ gradient ≤ 0 := by
  rw [neg_projectedGradient_dot_gradient memory orthonormal]
  exact neg_nonpos.mpr (dotProduct_self_nonnegative_local _)

/-- It is a strict descent direction exactly when some plastic component
survives the projection. -/
theorem neg_projectedGradient_dot_gradient_neg
    (memory : Matrix Coordinate Basis ℝ)
    (orthonormal : HasOrthonormalColumns memory)
    (gradient : Coordinate → ℝ)
    (nonzero : projectedGradient memory gradient ≠ 0) :
    (-projectedGradient memory gradient) ⬝ᵥ gradient < 0 := by
  rw [neg_projectedGradient_dot_gradient memory orthonormal]
  have normSqNonnegative :
      0 ≤ projectedGradient memory gradient ⬝ᵥ
        projectedGradient memory gradient :=
    dotProduct_self_nonnegative_local _
  have normSqNonzero :
      projectedGradient memory gradient ⬝ᵥ
          projectedGradient memory gradient ≠ 0 := by
    intro normSqZero
    exact nonzero (dotProduct_self_eq_zero.mp normSqZero)
  exact neg_lt_zero.mpr (lt_of_le_of_ne normSqNonnegative
    (Ne.symm normSqNonzero))

omit [DecidableEq Basis] in
/-- Zero memory recovers the ordinary current-task gradient. -/
theorem zeroMemory_projectedGradient
    (gradient : Coordinate → ℝ) :
    projectedGradient (0 : Matrix Coordinate Basis ℝ) gradient =
      gradient := by
  simp [projectedGradient, residualProjector, projector]

/-- A complete coordinate basis removes every gradient and therefore every
strictly improving first-order direction. -/
theorem identityMemory_erases_gradient
    (gradient : Coordinate → ℝ) :
    projectedGradient (1 : Matrix Coordinate Coordinate ℝ) gradient =
      0 := by
  simp [projectedGradient, residualProjector, projector]

/-! ## Executable positive and negative fixtures -/

/-- Storing the first coordinate preserves it and leaves a second-coordinate
gradient live, with exact descent margin four. -/
theorem firstAxisMemory_projects_to_second :
    let memory : Matrix (Fin 2) Unit ℝ :=
      fun coordinate _ => if coordinate = 0 then 1 else 0
    let gradient : Fin 2 → ℝ :=
      fun coordinate => if coordinate = 0 then 1 else 2
    HasOrthonormalColumns memory ∧
      projectedGradient memory gradient =
        (fun coordinate => if coordinate = 0 then 0 else 2) ∧
      (-projectedGradient memory gradient) ⬝ᵥ gradient = -4 := by
  dsimp
  constructor
  · ext first second
    cases first
    cases second
    norm_num [HasOrthonormalColumns, Matrix.mul_apply,
      Fin.sum_univ_two]
  · constructor
    · funext coordinate
      fin_cases coordinate <;>
        norm_num [projectedGradient, residualProjector, projector,
          Matrix.mulVec, Matrix.mul_apply, dotProduct,
          Fin.sum_univ_two]
    · norm_num [projectedGradient, residualProjector, projector,
        Matrix.mulVec, Matrix.mul_apply, dotProduct,
        Fin.sum_univ_two]

/-- Orthonormality is load-bearing.  In one dimension a stored vector of
length two produces the operator `I-4I=-3I`; following the negative nominal
projected gradient then has positive directional derivative and is strict
ascent. -/
theorem nonorthonormal_scalar_memory_reverses_descent :
    let memory : Matrix Unit Unit ℝ := fun _ _ => 2
    let gradient : Unit → ℝ := fun _ => 1
    ¬ HasOrthonormalColumns memory ∧
      projectedGradient memory gradient = (fun _ => -3) ∧
      (-projectedGradient memory gradient) ⬝ᵥ gradient = 3 := by
  dsimp
  constructor
  · intro orthonormal
    have entry := congr_fun (congr_fun orthonormal ()) ()
    norm_num [HasOrthonormalColumns, Matrix.mul_apply] at entry
  · constructor
    · funext coordinate
      cases coordinate
      norm_num [projectedGradient, residualProjector, projector,
        Matrix.mulVec, Matrix.mul_apply, dotProduct]
    · norm_num [projectedGradient, residualProjector, projector,
        Matrix.mulVec, Matrix.mul_apply, dotProduct]

#print axioms neg_projectedGradient_dot_gradient
#print axioms neg_projectedGradient_dot_gradient_neg
#print axioms firstAxisMemory_projects_to_second
#print axioms nonorthonormal_scalar_memory_reverses_descent

end

end OrthogonalGradientProjection

end Mettapedia.MachineLearning.ContinualLearning
