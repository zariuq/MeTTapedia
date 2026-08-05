import Mettapedia.MachineLearning.ContinualLearning.GradientProjectionMemory
import Mettapedia.MachineLearning.ContinualLearning.OrthogonalGradientRetention
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.LowRankAdaptation

/-!
# Interference-free low-rank adaptation

InfLoRA freezes a dimensionality-reduction factor `down` and trains only the
output factor of a LoRA branch.  For one sample, the induced dense-weight
gradient is

`denseGradient * (downᵀ * down)`.

This file recovers that identity and makes its hypotheses explicit.
`downᵀ * down` is an orthogonal projector only when the rows of `down` are
orthonormal, as they are when selected from the source's SVD basis.  Under
that hypothesis the update is exactly dense fine-tuning restricted to the
declared row subspace.  A bridge to gradient-projection memory identifies the
same update when that row projector is the residual projector of the stored
old-task subspace.

Two retention levels are kept separate.  If `down` annihilates a particular
old activation, every finite low-rank branch value preserves the corresponding
linear output exactly.  Orthogonality to an old loss gradient gives only a
first-order statement; an existing nonlinear fixture is re-exposed to show
that it does not by itself preserve finite-step loss.

The construction recovers Proposition 1 and Equations (2)--(8) of Liang and
Li, *InfLoRA: Interference-Free Low-Rank Adaptation for Continual Learning*
(2024).  It does not assert that a finite nonlinear task loss is preserved,
that the estimated old/new gradient spaces are exact, or that a selected
subspace retains enough plasticity for the new task.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

open Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace InterferenceFreeLowRankAdaptation

noncomputable section

variable {Input Output : Type*} {rankBudget : ℕ}
  [Fintype Input]

/-- One-sample dense gradient `outputGradient * inputᵀ`. -/
def sampleDenseGradient
    (outputGradient : Output → ℝ) (input : Input → ℝ) :
    Matrix Output Input ℝ :=
  Matrix.vecMulVec outputGradient input

/-- Gradient of the trainable output factor when `down` remains frozen. -/
def outputFactorGradient
    (outputGradient : Output → ℝ) (input : Input → ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    Matrix Output (Fin rankBudget) ℝ :=
  sampleDenseGradient outputGradient input * down.transpose

/-- Dense-weight gradient induced by changing only the output factor. -/
def inducedWeightGradient
    (outputGradient : Output → ℝ) (input : Input → ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    Matrix Output Input ℝ :=
  outputFactorGradient outputGradient input down * down

/-- The row-space operator selected by the frozen input factor. -/
def rowProjector (down : Matrix (Fin rankBudget) Input ℝ) :
    Matrix Input Input ℝ :=
  down.transpose * down

/-- Source Proposition 1, before the orthonormality qualification: changing
the output factor induces the dense gradient followed by `downᵀ * down`. -/
theorem inducedWeightGradient_eq_dense_mul_rowProjector
    (outputGradient : Output → ℝ) (input : Input → ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    inducedWeightGradient outputGradient input down =
      sampleDenseGradient outputGradient input * rowProjector down := by
  simp [inducedWeightGradient, outputFactorGradient, rowProjector,
    Matrix.mul_assoc]

/-- The induced gradient is itself an operational unit-scale low-rank update. -/
theorem inducedWeightGradient_eq_lowRankDelta
    (outputGradient : Output → ℝ) (input : Input → ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) :
    inducedWeightGradient outputGradient input down =
      lowRankDelta 1
        (outputFactorGradient outputGradient input down) down := by
  simp [inducedWeightGradient, lowRankDelta]

/-- Load-bearing SVD hypothesis: the rows of the frozen factor are
orthonormal. -/
def HasOrthonormalRows
    (down : Matrix (Fin rankBudget) Input ℝ) : Prop :=
  down * down.transpose = 1

/-- Row orthonormality is column orthonormality of the transposed basis used
by gradient-projection memory. -/
theorem hasOrthonormalRows_iff_transpose_hasOrthonormalColumns
    (down : Matrix (Fin rankBudget) Input ℝ) :
    HasOrthonormalRows down ↔
      GradientProjectionMemory.HasOrthonormalColumns down.transpose := by
  simp [HasOrthonormalRows,
    GradientProjectionMemory.HasOrthonormalColumns]

/-- With orthonormal rows, the source's row-space operator is idempotent. -/
theorem rowProjector_idempotent
    [DecidableEq Input]
    (down : Matrix (Fin rankBudget) Input ℝ)
    (orthonormal : HasOrthonormalRows down) :
    rowProjector down * rowProjector down = rowProjector down := by
  have transposedOrthonormal :
      GradientProjectionMemory.HasOrthonormalColumns down.transpose :=
    (hasOrthonormalRows_iff_transpose_hasOrthonormalColumns down).mp
      orthonormal
  simpa [rowProjector, GradientProjectionMemory.projector] using
    GradientProjectionMemory.projector_idempotent
      down.transpose transposedOrthonormal

omit [Fintype Input] in
/-- The row-space operator is symmetric even before orthonormalization. -/
@[simp] theorem rowProjector_transpose
    (down : Matrix (Fin rankBudget) Input ℝ) :
    (rowProjector down).transpose = rowProjector down := by
  simp [rowProjector, Matrix.transpose_mul]

/-- Exact bridge to the source's GPM implementation: if the selected row
projector equals the residual projector of old-task memory, output-factor
training induces exactly the GPM-projected dense gradient. -/
theorem inducedWeightGradient_eq_fullyConnectedUpdate
    {OldBasis : Type*} [Fintype OldBasis]
    [DecidableEq Input] [DecidableEq OldBasis]
    (oldMemory : Matrix Input OldBasis ℝ)
    (outputGradient : Output → ℝ) (input : Input → ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ)
    (complement :
      rowProjector down =
        GradientProjectionMemory.residualProjector oldMemory) :
    inducedWeightGradient outputGradient input down =
      GradientProjectionMemory.fullyConnectedUpdate oldMemory
        (sampleDenseGradient outputGradient input) := by
  rw [inducedWeightGradient_eq_dense_mul_rowProjector, complement]
  exact
    (GradientProjectionMemory.fullyConnectedUpdate_eq_mul_residualProjector
      oldMemory (sampleDenseGradient outputGradient input)).symm

/-! ## Exact linear retention versus first-order retention -/

/-- If the frozen input factor annihilates an old activation, its low-rank
branch output is exactly zero for every output factor and scale. -/
theorem lowRankDelta_mulVec_eq_zero_of_down_mulVec_eq_zero
    (scale : ℝ) (up : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) (oldInput : Input → ℝ)
    (annihilates : down.mulVec oldInput = 0) :
    (lowRankDelta scale up down).mulVec oldInput = 0 := by
  rw [lowRankDelta, ← Matrix.mulVec_mulVec, annihilates]
  simp

/-- Consequently, merging the branch preserves the frozen linear output on
that old activation exactly, not merely to first order. -/
theorem mergedLowRankWeight_mulVec_eq_base_of_down_mulVec_eq_zero
    (base : Matrix Output Input ℝ)
    (scale : ℝ) (up : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ) (oldInput : Input → ℝ)
    (annihilates : down.mulVec oldInput = 0) :
    (mergedLowRankWeight base scale up down).mulVec oldInput =
      base.mulVec oldInput := by
  rw [mergedLowRankWeight, Matrix.add_mulVec,
    lowRankDelta_mulVec_eq_zero_of_down_mulVec_eq_zero
      scale up down oldInput annihilates]
  simp

/-- Frobenius pairing used to state first-order interference. -/
def frobeniusPairing
    [Fintype Output]
    (first second : Matrix Output Input ℝ) : ℝ :=
  Matrix.trace (first.transpose * second)

/-- Moving a right factor across the Frobenius pairing transposes it. -/
theorem frobeniusPairing_mul_right
    {Middle : Type*} [Fintype Output] [Fintype Middle]
    (first : Matrix Output Input ℝ)
    (second : Matrix Output Middle ℝ)
    (right : Matrix Middle Input ℝ) :
    frobeniusPairing first (second * right) =
      Matrix.trace ((first * right.transpose).transpose * second) := by
  unfold frobeniusPairing
  calc
    Matrix.trace (first.transpose * (second * right)) =
        Matrix.trace ((first.transpose * second) * right) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace (right * (first.transpose * second)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((right * first.transpose) * second) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace ((first * right.transpose).transpose * second) := by
      simp [Matrix.transpose_mul]

/-- If the selected rows are orthogonal to an old dense gradient, every
output-factor change is first-order orthogonal to that old gradient. -/
theorem frobeniusPairing_old_mul_outputFactor_eq_zero
    [Fintype Output]
    (oldGradient : Matrix Output Input ℝ)
    (upChange : Matrix Output (Fin rankBudget) ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ)
    (orthogonal : oldGradient * down.transpose = 0) :
    frobeniusPairing oldGradient (upChange * down) = 0 := by
  rw [frobeniusPairing_mul_right, orthogonal]
  simp

/-- In particular, the InfLoRA-induced dense gradient has zero first-order
pairing with every old gradient annihilated by the frozen row basis. -/
theorem inducedWeightGradient_old_firstOrderInterference_eq_zero
    [Fintype Output]
    (oldGradient : Matrix Output Input ℝ)
    (outputGradient : Output → ℝ) (input : Input → ℝ)
    (down : Matrix (Fin rankBudget) Input ℝ)
    (orthogonal : oldGradient * down.transpose = 0) :
    frobeniusPairing oldGradient
        (inducedWeightGradient outputGradient input down) =
      0 := by
  exact frobeniusPairing_old_mul_outputFactor_eq_zero
    oldGradient (outputFactorGradient outputGradient input down)
      down orthogonal

/-! ## Positive and negative executable fixtures -/

/-- A one-row adapter selecting the second coordinate preserves the first
coordinate's activation exactly while remaining live on the second. -/
theorem secondAxis_preserves_first_and_updates_second :
    let down : Matrix (Fin 1) (Fin 2) ℝ :=
      fun _ input => if input = 1 then 1 else 0
    let up : Matrix Unit (Fin 1) ℝ := fun _ _ => 3
    let first : Fin 2 → ℝ := fun input => if input = 0 then 1 else 0
    let second : Fin 2 → ℝ := fun input => if input = 1 then 1 else 0
    (lowRankDelta 1 up down).mulVec first = 0 ∧
      (lowRankDelta 1 up down).mulVec second = fun _ => 3 := by
  dsimp
  constructor <;>
    funext output <;>
    cases output <;>
    norm_num [lowRankDelta, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Fin.sum_univ_two]

omit [Fintype Input] in
/-- Full orthonormal row space recovers the unconstrained dense gradient. -/
theorem identityDown_recovers_dense_gradient
    {width : ℕ}
    (outputGradient : Output → ℝ) (input : Fin width → ℝ) :
    inducedWeightGradient outputGradient input
        (1 : Matrix (Fin width) (Fin width) ℝ) =
      sampleDenseGradient outputGradient input := by
  rw [inducedWeightGradient_eq_dense_mul_rowProjector]
  simp [rowProjector]

/-- Zero row space removes every induced dense-weight gradient. -/
theorem zeroDown_erases_induced_gradient
    (outputGradient : Output → ℝ) (input : Input → ℝ) :
    inducedWeightGradient outputGradient input
        (0 : Matrix (Fin rankBudget) Input ℝ) =
      0 := by
  simp [inducedWeightGradient, outputFactorGradient]

/-- Without row orthonormality, `downᵀ * down` need not be a projector and
can amplify rather than merely project a dense gradient. -/
theorem scalar_nonorthonormal_down_amplifies_by_four :
    let outputGradient : Unit → ℝ := fun _ => 1
    let input : Unit → ℝ := fun _ => 1
    let down : Matrix (Fin 1) Unit ℝ := fun _ _ => 2
    inducedWeightGradient outputGradient input down =
        (fun _ _ => 4) ∧
      rowProjector down * rowProjector down ≠ rowProjector down ∧
      ¬ HasOrthonormalRows down := by
  dsimp
  constructor
  · ext output inputIndex
    cases output
    cases inputIndex
    norm_num [inducedWeightGradient, outputFactorGradient,
      sampleDenseGradient, Matrix.vecMulVec, Matrix.mul_apply]
  · constructor
    · intro idempotent
      have entry := congrFun (congrFun idempotent ()) ()
      norm_num [rowProjector, Matrix.mul_apply] at entry
    · intro orthonormal
      have entry := congrFun (congrFun orthonormal 0) 0
      norm_num [HasOrthonormalRows, Matrix.mul_apply] at entry

/-- The exact nonlinear boundary already present in the continual-learning
theory: a zero old gradient is orthogonal to every update, yet a finite step
can change the old loss. -/
theorem firstOrderOrthogonality_does_not_imply_finiteLossRetention :
    HasDerivAt nonlinearQuadraticReadout 0 0 ∧
      nonlinearQuadraticReadout (0 + 1) ≠
        nonlinearQuadraticReadout 0 :=
  nonlinear_stationary_gradient_does_not_imply_no_forgetting

#print axioms inducedWeightGradient_eq_dense_mul_rowProjector
#print axioms rowProjector_idempotent
#print axioms inducedWeightGradient_eq_fullyConnectedUpdate
#print axioms mergedLowRankWeight_mulVec_eq_base_of_down_mulVec_eq_zero
#print axioms inducedWeightGradient_old_firstOrderInterference_eq_zero
#print axioms secondAxis_preserves_first_and_updates_second
#print axioms scalar_nonorthonormal_down_amplifies_by_four
#print axioms firstOrderOrthogonality_does_not_imply_finiteLossRetention

end

end InterferenceFreeLowRankAdaptation

end Mettapedia.MachineLearning.ContinualLearning
