import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromStability
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Routed CAROM: a constructed common metric for commuting nilpotent commands

The general commuting-Schur-stable common-Lyapunov theorem requires a
simultaneous triangularization and metric construction.  This file seals its
smallest nontrivial finite-dimensional rung: two commuting square-zero
commands.

The metric records the current state, each one-command image, and the joint
image.  Commutation makes either command shift those components one level
forward, while square-zero nilpotence kills the boundary.  With geometric
weights `1, 2, 4`, both commands contract the same positive-definite quadratic
energy by a factor of `1/2`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function
open scoped Matrix

namespace RoutedCarom

universe uIndex

section TwoSquareZeroCommands

variable {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- Select one of two command matrices. -/
noncomputable def twoCommandTransition
    (first second : Matrix Index Index ℝ) : Bool → Matrix Index Index ℝ
  | false => first
  | true => second

/-- Shared metric for two commuting square-zero commands. -/
noncomputable def commutingSquareZeroMetric
    (first second : Matrix Index Index ℝ) : Matrix Index Index ℝ :=
  1 + 2 • (first.transpose * first + second.transpose * second) +
    4 • ((first * second).transpose * (first * second))

/-- Coordinate form of the shared energy. -/
theorem commutingSquareZeroMetric_energy_eq
    (first second : Matrix Index Index ℝ) (state : Index → ℝ) :
    quadraticEnergy (commutingSquareZeroMetric first second) state =
      dotProduct state state +
        2 * dotProduct (first *ᵥ state) (first *ᵥ state) +
        2 * dotProduct (second *ᵥ state) (second *ᵥ state) +
        4 * dotProduct ((first * second) *ᵥ state)
          ((first * second) *ᵥ state) := by
  simp only [quadraticEnergy, commutingSquareZeroMetric, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul]
  have firstEnergy :
      dotProduct state ((first.transpose * first) *ᵥ state) =
        dotProduct (first *ᵥ state) (first *ᵥ state) := by
    rw [← Matrix.mulVec_mulVec]
    exact Matrix.dotProduct_transpose_mulVec first state (first *ᵥ state)
  have secondEnergy :
      dotProduct state ((second.transpose * second) *ᵥ state) =
        dotProduct (second *ᵥ state) (second *ᵥ state) := by
    rw [← Matrix.mulVec_mulVec]
    exact Matrix.dotProduct_transpose_mulVec second state (second *ᵥ state)
  have jointEnergy :
      dotProduct state
          (((first * second).transpose * (first * second)) *ᵥ state) =
        dotProduct ((first * second) *ᵥ state)
          ((first * second) *ᵥ state) := by
    rw [← Matrix.mulVec_mulVec]
    exact Matrix.dotProduct_transpose_mulVec (first * second) state
      ((first * second) *ᵥ state)
  rw [firstEnergy, secondEnergy, jointEnergy]
  ring

omit [DecidableEq Index] in
/-- Euclidean self-dot-products are nonnegative. -/
theorem real_dotProduct_self_nonneg (state : Index → ℝ) :
    0 ≤ dotProduct state state := by
  exact Finset.sum_nonneg fun index _ => mul_self_nonneg (state index)

/-- The constructed energy is nonnegative without any commutation or
nilpotence assumption. -/
theorem commutingSquareZeroMetric_energy_nonneg
    (first second : Matrix Index Index ℝ) (state : Index → ℝ) :
    0 ≤ quadraticEnergy (commutingSquareZeroMetric first second) state := by
  rw [commutingSquareZeroMetric_energy_eq]
  have hState := real_dotProduct_self_nonneg state
  have hFirst := real_dotProduct_self_nonneg (first *ᵥ state)
  have hSecond := real_dotProduct_self_nonneg (second *ᵥ state)
  have hJoint := real_dotProduct_self_nonneg ((first * second) *ᵥ state)
  positivity

/-- The identity term makes the constructed quadratic energy strictly
positive on nonzero states. -/
theorem commutingSquareZeroMetric_energy_pos
    (first second : Matrix Index Index ℝ) {state : Index → ℝ}
    (state_ne_zero : state ≠ 0) :
    0 < quadraticEnergy (commutingSquareZeroMetric first second) state := by
  rw [commutingSquareZeroMetric_energy_eq]
  have hStateNonneg := real_dotProduct_self_nonneg state
  have hFirst := real_dotProduct_self_nonneg (first *ᵥ state)
  have hSecond := real_dotProduct_self_nonneg (second *ᵥ state)
  have hJoint := real_dotProduct_self_nonneg ((first * second) *ᵥ state)
  have hStateNe : dotProduct state state ≠ 0 := by
    simpa using state_ne_zero
  have hStatePos : 0 < dotProduct state state :=
    lt_of_le_of_ne hStateNonneg (Ne.symm hStateNe)
  positivity

/-- Matrix-level form of strict positivity: the constructed metric is
positive definite, not merely nonnegative on the states used below. -/
theorem commutingSquareZeroMetric_posDef
    (first second : Matrix Index Index ℝ) :
    (commutingSquareZeroMetric first second).PosDef := by
  have firstSymm : (first.transpose * first).IsSymm :=
    Matrix.isSymm_transpose_mul_self first
  have secondSymm : (second.transpose * second).IsSymm :=
    Matrix.isSymm_transpose_mul_self second
  have jointSymm :
      ((first * second).transpose * (first * second)).IsSymm :=
    Matrix.isSymm_transpose_mul_self (first * second)
  have metricSymm : (commutingSquareZeroMetric first second).IsSymm := by
    simpa only [commutingSquareZeroMetric] using
      (Matrix.isSymm_one.add
        ((firstSymm.add secondSymm).smul (2 : ℕ))).add
          (jointSymm.smul (4 : ℕ))
  exact Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr metricSymm) fun state state_ne_zero => by
      simpa [quadraticEnergy] using
        commutingSquareZeroMetric_energy_pos first second state_ne_zero

/-- Applying the first command shifts the shared energy down one weighted
level. -/
theorem commutingSquareZeroMetric_first_energy_eq
    (first second : Matrix Index Index ℝ)
    (first_square_zero : first * first = 0)
    (commute : Commute first second) (state : Index → ℝ) :
    quadraticEnergy (commutingSquareZeroMetric first second)
        (first *ᵥ state) =
      dotProduct (first *ᵥ state) (first *ᵥ state) +
        2 * dotProduct ((first * second) *ᵥ state)
          ((first * second) *ᵥ state) := by
  rw [commutingSquareZeroMetric_energy_eq]
  have first_first : first *ᵥ (first *ᵥ state) = 0 := by
    rw [Matrix.mulVec_mulVec, first_square_zero]
    simp
  have second_first : second *ᵥ (first *ᵥ state) =
      (first * second) *ᵥ state := by
    rw [Matrix.mulVec_mulVec, commute.eq]
  have joint_first : (first * second) *ᵥ (first *ᵥ state) = 0 := by
    rw [Matrix.mulVec_mulVec]
    have : (first * second) * first = 0 := by
      calc
        (first * second) * first = first * (second * first) := by
          rw [Matrix.mul_assoc]
        _ = first * (first * second) := by rw [commute.eq]
        _ = (first * first) * second := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [first_square_zero, zero_mul]
    rw [this]
    simp
  rw [first_first, second_first, joint_first]
  simp

/-- Applying the second command shifts the shared energy down one weighted
level. -/
theorem commutingSquareZeroMetric_second_energy_eq
    (first second : Matrix Index Index ℝ)
    (second_square_zero : second * second = 0)
    (state : Index → ℝ) :
    quadraticEnergy (commutingSquareZeroMetric first second)
        (second *ᵥ state) =
      dotProduct (second *ᵥ state) (second *ᵥ state) +
        2 * dotProduct ((first * second) *ᵥ state)
      ((first * second) *ᵥ state) := by
  rw [commutingSquareZeroMetric_energy_eq]
  have first_second : first *ᵥ (second *ᵥ state) =
      (first * second) *ᵥ state := by
    rw [Matrix.mulVec_mulVec]
  have second_second : second *ᵥ (second *ᵥ state) = 0 := by
    rw [Matrix.mulVec_mulVec, second_square_zero]
    simp
  have joint_second : (first * second) *ᵥ (second *ᵥ state) = 0 := by
    rw [Matrix.mulVec_mulVec]
    have : (first * second) * second = 0 := by
      calc
        (first * second) * second = first * (second * second) := by
          rw [Matrix.mul_assoc]
        _ = 0 := by rw [second_square_zero, mul_zero]
    rw [this]
    simp
  rw [first_second, second_second, joint_second]
  simp

/-- Each commuting square-zero command contracts the constructed shared
energy by rate `1/2`. -/
theorem commutingSquareZeroMetric_contracts
    (first second : Matrix Index Index ℝ)
    (first_square_zero : first * first = 0)
    (second_square_zero : second * second = 0)
    (commute : Commute first second) (command : Bool) (state : Index → ℝ) :
    quadraticEnergy (commutingSquareZeroMetric first second)
        (twoCommandTransition first second command *ᵥ state) ≤
      (1 / 2 : ℝ) *
        quadraticEnergy (commutingSquareZeroMetric first second) state := by
  have hState := real_dotProduct_self_nonneg state
  have hFirst := real_dotProduct_self_nonneg (first *ᵥ state)
  have hSecond := real_dotProduct_self_nonneg (second *ᵥ state)
  have hJoint := real_dotProduct_self_nonneg ((first * second) *ᵥ state)
  cases command with
  | false =>
      simp only [twoCommandTransition]
      rw [
        commutingSquareZeroMetric_first_energy_eq first second
          first_square_zero commute state,
        commutingSquareZeroMetric_energy_eq]
      linarith
  | true =>
      simp only [twoCommandTransition]
      rw [
        commutingSquareZeroMetric_second_energy_eq first second
          second_square_zero state,
        commutingSquareZeroMetric_energy_eq]
      linarith

/-- Constructive common quadratic Lyapunov certificate for two commuting
square-zero commands. -/
noncomputable def commutingSquareZeroCommonLyapunov
    (first second : Matrix Index Index ℝ)
    (first_square_zero : first * first = 0)
    (second_square_zero : second * second = 0)
    (commute : Commute first second) :
    CommonQuadraticLyapunov (twoCommandTransition first second) where
  metric := commutingSquareZeroMetric first second
  rate := 1 / 2
  rate_nonneg := by norm_num
  rate_lt_one := by norm_num
  energy_nonneg := commutingSquareZeroMetric_energy_nonneg first second
  contracts := commutingSquareZeroMetric_contracts first second
    first_square_zero second_square_zero commute

/-- Schedule-level crown: every finite switching sequence of the two commands
obeys the same geometric energy envelope. -/
theorem commutingSquareZero_allSchedules_energy_le
    (first second : Matrix Index Index ℝ)
    (first_square_zero : first * first = 0)
    (second_square_zero : second * second = 0)
    (commute : Commute first second)
    (schedule : List Bool) (initial : Index → ℝ) :
    quadraticEnergy (commutingSquareZeroMetric first second)
        (runLinearSchedule (twoCommandTransition first second) schedule initial) ≤
      (1 / 2 : ℝ) ^ schedule.length *
        quadraticEnergy (commutingSquareZeroMetric first second) initial := by
  exact (commutingSquareZeroCommonLyapunov first second first_square_zero
    second_square_zero commute).runLinearSchedule_energy_le schedule initial

/-! ## Executable positive and negative boundary fixtures -/

/-- First nonzero square-zero fixture. -/
noncomputable def commutingNilpotentA : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 0, 0]

/-- A distinct nonzero scalar multiple of the first fixture. -/
noncomputable def commutingNilpotentB : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 2; 0, 0]

theorem commutingNilpotentA_square_zero :
    commutingNilpotentA * commutingNilpotentA = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutingNilpotentA, Matrix.mul_apply, Fin.sum_univ_two]

theorem commutingNilpotentB_square_zero :
    commutingNilpotentB * commutingNilpotentB = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutingNilpotentB, Matrix.mul_apply, Fin.sum_univ_two]

theorem commutingNilpotentAB_commute :
    Commute commutingNilpotentA commutingNilpotentB := by
  rw [Commute]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutingNilpotentA, commutingNilpotentB,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem commutingNilpotentAB_distinct_nonzero :
    commutingNilpotentA ≠ 0 ∧ commutingNilpotentB ≠ 0 ∧
      commutingNilpotentA ≠ commutingNilpotentB := by
  constructor
  · intro h
    have := congr_fun (congr_fun h 0) 1
    norm_num [commutingNilpotentA] at this
  constructor
  · intro h
    have := congr_fun (congr_fun h 0) 1
    norm_num [commutingNilpotentB] at this
  · intro h
    have := congr_fun (congr_fun h 0) 1
    norm_num [commutingNilpotentA, commutingNilpotentB] at this

/-- Positive fixture: two distinct, nonzero, commuting square-zero commands
have an explicitly constructed shared strict quadratic contraction. -/
noncomputable def commutingNilpotentABCommonLyapunov :
    CommonQuadraticLyapunov
      (twoCommandTransition commutingNilpotentA commutingNilpotentB) :=
  commutingSquareZeroCommonLyapunov commutingNilpotentA commutingNilpotentB
    commutingNilpotentA_square_zero commutingNilpotentB_square_zero
    commutingNilpotentAB_commute

/-- The divergent square-zero pair from `RoutedCaromStability` violates the
new theorem's decisive hypothesis. -/
theorem divergentSwitches_not_commute :
    ¬ Commute divergentSwitchA divergentSwitchB := by
  intro h
  have hentry := congr_fun (congr_fun h.eq 0) 0
  norm_num [divergentSwitchA, divergentSwitchB,
    Matrix.mul_apply, Fin.sum_univ_two] at hentry

#print axioms commutingSquareZeroMetric_energy_eq
#print axioms commutingSquareZeroMetric_energy_pos
#print axioms commutingSquareZeroMetric_posDef
#print axioms commutingSquareZeroMetric_contracts
#print axioms commutingSquareZeroCommonLyapunov
#print axioms commutingSquareZero_allSchedules_energy_le
#print axioms commutingNilpotentABCommonLyapunov
#print axioms divergentSwitches_not_commute

end TwoSquareZeroCommands

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
