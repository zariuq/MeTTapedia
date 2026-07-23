import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromScalarShiftStability
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Routed CAROM: assembling common metrics across invariant blocks

Simultaneous generalized eigenspaces reduce a commuting matrix family to
invariant blocks.  This file supplies the complementary assembly theorem: a
common quadratic certificate on every block, with one shared rate, induces a
common certificate on the block-diagonal direct sum.

The theorem is stated for a finite dependent family of block index types, so
it can later consume generalized eigenspaces of unequal dimensions.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function
open scoped Matrix BigOperators

namespace RoutedCarom

universe uCommand uBlock uIndex

section BlockAssembly

variable {Command : Type uCommand}
variable {Block : Type uBlock} [Fintype Block] [DecidableEq Block]
variable {Index : Block → Type uIndex}
variable [∀ block, Fintype (Index block)] [∀ block, DecidableEq (Index block)]

/-- Restrict a state on a dependent direct sum to one block. -/
def blockState (state : (Σ block, Index block) → ℝ) (block : Block) :
    Index block → ℝ :=
  fun index => state ⟨block, index⟩

/-- Assemble a command family from invariant diagonal blocks. -/
noncomputable def blockDiagonalTransition
    (transition : ∀ block, Command → Matrix (Index block) (Index block) ℝ) :
    Command → Matrix (Σ block, Index block) (Σ block, Index block) ℝ :=
  fun command => Matrix.blockDiagonal' fun block => transition block command

omit [∀ block, DecidableEq (Index block)] in
/-- A block-diagonal matrix acts independently on every restricted state. -/
theorem blockDiagonal_mulVec_apply
    (matrix : ∀ block, Matrix (Index block) (Index block) ℝ)
    (state : (Σ block, Index block) → ℝ)
    (block : Block) (index : Index block) :
    (Matrix.blockDiagonal' matrix *ᵥ state) ⟨block, index⟩ =
      (matrix block *ᵥ blockState state block) index := by
  simp only [Matrix.mulVec, dotProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma,
    Matrix.blockDiagonal'_apply]
  rw [Fintype.sum_eq_single block]
  · simp [blockState]
  · intro other other_ne
    simp [other_ne.symm]

omit [∀ block, DecidableEq (Index block)] in
/-- Restricting the response of a block-diagonal command recovers the local
block response. -/
theorem blockState_blockDiagonalTransition_mulVec
    (transition : ∀ block, Command → Matrix (Index block) (Index block) ℝ)
    (command : Command) (state : (Σ block, Index block) → ℝ)
    (block : Block) :
    blockState (blockDiagonalTransition transition command *ᵥ state) block =
      transition block command *ᵥ blockState state block := by
  funext index
  exact blockDiagonal_mulVec_apply (fun b => transition b command) state block index

omit [∀ block, DecidableEq (Index block)] in
/-- The quadratic energy of a block-diagonal metric is the sum of its block
energies. -/
theorem quadraticEnergy_blockDiagonal
    (metric : ∀ block, Matrix (Index block) (Index block) ℝ)
    (state : (Σ block, Index block) → ℝ) :
    quadraticEnergy (Matrix.blockDiagonal' metric) state =
      ∑ block, quadraticEnergy (metric block) (blockState state block) := by
  simp only [quadraticEnergy, dotProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro block _
  apply Finset.sum_congr rfl
  intro index _
  rw [blockDiagonal_mulVec_apply]
  rfl

/-- Shared-rate local certificates assemble into one common quadratic
Lyapunov certificate on their finite dependent direct sum. -/
noncomputable def blockDiagonalCommonLyapunov
    (transition : ∀ block, Command → Matrix (Index block) (Index block) ℝ)
    (metric : ∀ block, Matrix (Index block) (Index block) ℝ)
    (rate : ℝ)
    (rate_nonneg : 0 ≤ rate)
    (rate_lt_one : rate < 1)
    (energy_nonneg : ∀ block state,
      0 ≤ quadraticEnergy (metric block) state)
    (contracts : ∀ block command state,
      quadraticEnergy (metric block) (transition block command *ᵥ state) ≤
        rate * quadraticEnergy (metric block) state) :
    CommonQuadraticLyapunov (blockDiagonalTransition transition) where
  metric := Matrix.blockDiagonal' metric
  rate := rate
  rate_nonneg := rate_nonneg
  rate_lt_one := rate_lt_one
  energy_nonneg := by
    intro state
    rw [quadraticEnergy_blockDiagonal]
    exact Finset.sum_nonneg fun block _ => energy_nonneg block _
  contracts := by
    intro command state
    rw [quadraticEnergy_blockDiagonal, quadraticEnergy_blockDiagonal]
    simp_rw [blockState_blockDiagonalTransition_mulVec transition command state]
    calc
      ∑ block, quadraticEnergy (metric block)
          (transition block command *ᵥ blockState state block) ≤
          ∑ block, rate * quadraticEnergy (metric block) (blockState state block) :=
        Finset.sum_le_sum fun block _ => contracts block command _
      _ = rate * ∑ block,
          quadraticEnergy (metric block) (blockState state block) := by
        rw [Finset.mul_sum]

/-! ## Positive and negative fixtures -/

/-- Two different stable scalar blocks. -/
noncomputable def stableBlockScalar (block : Bool) : ℝ :=
  if block then 1 / 3 else 1 / 2

noncomputable def stableBlockTransition
    (block : Bool) (_ : Unit) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => stableBlockScalar block

noncomputable def unitBlockMetric (_ : Bool) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => 1

/-- The slower half-contraction determines one rate shared with the faster
third-contraction block. -/
noncomputable def stableTwoBlockCommonLyapunov :
    CommonQuadraticLyapunov
      (blockDiagonalTransition (Index := fun _ : Bool => Fin 1)
        stableBlockTransition) :=
  blockDiagonalCommonLyapunov stableBlockTransition unitBlockMetric
    (1 / 4) (by norm_num) (by norm_num)
    (by
      intro block state
      simp [quadraticEnergy, unitBlockMetric, Matrix.mulVec, dotProduct]
      nlinarith [sq_nonneg (state 0)])
    (by
      intro block command state
      cases block <;>
        simp [quadraticEnergy, stableBlockTransition, stableBlockScalar,
          unitBlockMetric, Matrix.mulVec, dotProduct] <;>
        nlinarith [sq_nonneg (state 0)])

theorem stableTwoBlock_allSchedules_energy_le
    (schedule : List Unit)
    (initial : (Σ _ : Bool, Fin 1) → ℝ) :
    quadraticEnergy stableTwoBlockCommonLyapunov.metric
        (runLinearSchedule
          (blockDiagonalTransition (Index := fun _ : Bool => Fin 1)
            stableBlockTransition) schedule initial) ≤
      (1 / 4 : ℝ) ^ schedule.length *
        quadraticEnergy stableTwoBlockCommonLyapunov.metric initial := by
  exact stableTwoBlockCommonLyapunov.runLinearSchedule_energy_le schedule initial

/-- Replacing the second stable block by a factor-two expansion. -/
noncomputable def unstableBlockScalar (block : Bool) : ℝ :=
  if block then 2 else 1 / 2

noncomputable def unstableBlockTransition
    (block : Bool) (_ : Unit) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => unstableBlockScalar block

/-- State supported only on the expanding block. -/
noncomputable def expandingBlockState : (Σ _ : Bool, Fin 1) → ℝ
  | ⟨false, _⟩ => 0
  | ⟨true, _⟩ => 1

theorem expandingBlockState_energy :
    quadraticEnergy (Matrix.blockDiagonal' unitBlockMetric)
      expandingBlockState = 1 := by
  rw [quadraticEnergy_blockDiagonal]
  norm_num [blockState, expandingBlockState, quadraticEnergy,
    unitBlockMetric, Matrix.mulVec, dotProduct]

theorem expandingBlockState_energy_after :
    quadraticEnergy (Matrix.blockDiagonal' unitBlockMetric)
      (blockDiagonalTransition (Index := fun _ : Bool => Fin 1)
        unstableBlockTransition () *ᵥ expandingBlockState) = 4 := by
  rw [quadraticEnergy_blockDiagonal]
  simp_rw [blockState_blockDiagonalTransition_mulVec
    unstableBlockTransition () expandingBlockState]
  norm_num [blockState, expandingBlockState, quadraticEnergy,
    unstableBlockTransition, unstableBlockScalar, unitBlockMetric,
    Matrix.mulVec, dotProduct]

/-- One expanding block prevents the unit block metric from having any strict
common rate, even though the other block is contractive. -/
theorem expandingBlock_refutes_strictUnitMetric :
    ¬ ∃ rate : ℝ, rate < 1 ∧
      ∀ state : (Σ _ : Bool, Fin 1) → ℝ,
        quadraticEnergy (Matrix.blockDiagonal' unitBlockMetric)
            (blockDiagonalTransition (Index := fun _ : Bool => Fin 1)
              unstableBlockTransition () *ᵥ state) ≤
          rate * quadraticEnergy (Matrix.blockDiagonal' unitBlockMetric) state := by
  rintro ⟨rate, rate_lt_one, contracts⟩
  have contradiction := contracts expandingBlockState
  rw [expandingBlockState_energy_after, expandingBlockState_energy] at contradiction
  nlinarith

#print axioms blockDiagonal_mulVec_apply
#print axioms quadraticEnergy_blockDiagonal
#print axioms blockDiagonalCommonLyapunov
#print axioms stableTwoBlockCommonLyapunov
#print axioms stableTwoBlock_allSchedules_energy_le
#print axioms expandingBlock_refutes_strictUnitMetric

end BlockAssembly

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
