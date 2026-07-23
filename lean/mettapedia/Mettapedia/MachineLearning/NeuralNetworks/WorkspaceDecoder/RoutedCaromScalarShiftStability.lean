import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromJointNilpotentStability

/-!
# Routed CAROM: scalar contractions with jointly nilpotent residuals

This file advances beyond purely nilpotent command maps without claiming the
full commuting-Schur theorem.  Each command is decomposed as a scalar identity
shift plus a routed residual.  The residual family is jointly nilpotent, while
the scalar part supplies persistent contraction.

Scaling the residual family before constructing its recursive word metric
makes the residual energy contribution arbitrarily small without changing
finite extinction.  A parallelogram bound then supplies one explicit common
quadratic metric for the shifted family.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function
open scoped Matrix BigOperators

namespace RoutedCarom

universe uCommand uIndex

section ScalarShift

variable {Command : Type uCommand} [Fintype Command] [DecidableEq Command]
variable {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

/-- Uniformly scale every routed residual command. -/
noncomputable def scaledTransition
    (scale : ℝ) (transition : Command → Matrix Index Index ℝ) :
    Command → Matrix Index Index ℝ :=
  fun command => scale • transition command

/-- Add a command-dependent scalar identity component to a residual family. -/
noncomputable def scalarShiftedTransition
    (coefficient : Command → ℝ)
    (residual : Command → Matrix Index Index ℝ) :
    Command → Matrix Index Index ℝ :=
  fun command => coefficient command • (1 : Matrix Index Index ℝ) + residual command

omit [Fintype Command] [DecidableEq Command] [DecidableEq Index] in
/-- Linear schedule execution commutes with scalar multiplication of the
initial state. -/
theorem runLinearSchedule_smul_state
    (transition : Command → Matrix Index Index ℝ)
    (schedule : List Command) (scalar : ℝ) (state : Index → ℝ) :
    runLinearSchedule transition schedule (scalar • state) =
      scalar • runLinearSchedule transition schedule state := by
  induction schedule generalizing state with
  | nil => rfl
  | cons command schedule ih =>
      simp only [runLinearSchedule, Matrix.mulVec_smul]
      exact ih (transition command *ᵥ state)

omit [Fintype Command] [DecidableEq Command] [DecidableEq Index] in
/-- Executing uniformly scaled commands multiplies the endpoint by one scale
factor per command. -/
theorem runLinearSchedule_scaledTransition
    (scale : ℝ) (transition : Command → Matrix Index Index ℝ)
    (schedule : List Command) (state : Index → ℝ) :
    runLinearSchedule (scaledTransition scale transition) schedule state =
      scale ^ schedule.length • runLinearSchedule transition schedule state := by
  induction schedule generalizing state with
  | nil => simp [runLinearSchedule]
  | cons command schedule ih =>
      rw [runLinearSchedule]
      simp only [scaledTransition, Matrix.smul_mulVec]
      rw [runLinearSchedule_smul_state, ih]
      simp only [runLinearSchedule, List.length_cons, pow_succ, smul_smul]
      rw [mul_comm]

omit [Fintype Command] [DecidableEq Command] [DecidableEq Index] in
/-- Uniform scaling preserves joint nilpotence at the same depth. -/
theorem JointlyNilpotentAt.scaledTransition
    {transition : Command → Matrix Index Index ℝ} {depth : ℕ}
    (jointlyNilpotent : JointlyNilpotentAt transition depth)
    (scale : ℝ) :
    JointlyNilpotentAt (scaledTransition scale transition) depth := by
  intro state schedule schedule_length
  rw [runLinearSchedule_scaledTransition]
  rw [jointlyNilpotent state schedule schedule_length, smul_zero]

omit [Fintype Command] [DecidableEq Command] [DecidableEq Index] in
/-- Quadratic energy is homogeneous of degree two in the state. -/
theorem quadraticEnergy_state_smul
    (metric : Matrix Index Index ℝ) (scalar : ℝ) (state : Index → ℝ) :
    quadraticEnergy metric (scalar • state) =
      scalar ^ 2 * quadraticEnergy metric state := by
  simp only [quadraticEnergy, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul]
  ring

omit [Fintype Command] [DecidableEq Command] [DecidableEq Index] in
/-- Nonnegativity of a quadratic form gives the two-term parallelogram upper
bound without requiring a coordinatewise norm estimate. -/
theorem quadraticEnergy_add_le_two
    (metric : Matrix Index Index ℝ)
    (energy_nonneg : ∀ state, 0 ≤ quadraticEnergy metric state)
    (first second : Index → ℝ) :
    quadraticEnergy metric (first + second) ≤
      2 * quadraticEnergy metric first + 2 * quadraticEnergy metric second := by
  have difference_nonneg := energy_nonneg (first - second)
  have parallelogram :
      quadraticEnergy metric (first + second) +
          quadraticEnergy metric (first - second) =
        2 * quadraticEnergy metric first +
          2 * quadraticEnergy metric second := by
    simp only [quadraticEnergy, Matrix.mulVec_add, Matrix.mulVec_sub,
      add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
    ring
  linarith

/-- The metric built from a scaled jointly nilpotent family makes the original
residual family contract with an explicit inverse-square scale factor. -/
theorem jointlyNilpotent_residual_energy_le
    (residual : Command → Matrix Index Index ℝ)
    (depth : ℕ)
    (jointlyNilpotent : JointlyNilpotentAt residual (depth + 2))
    (scale : ℝ) (scale_pos : 0 < scale)
    (command : Command) (state : Index → ℝ) :
    quadraticEnergy
        (jointNilpotentMetric (scaledTransition scale residual) (depth + 1))
        (residual command *ᵥ state) ≤
      (1 / (2 * scale ^ 2)) *
        quadraticEnergy
          (jointNilpotentMetric (scaledTransition scale residual) (depth + 1)) state := by
  have scaledJoint := jointlyNilpotent.scaledTransition scale
  have contraction := jointlyNilpotentMetric_contracts
    (scaledTransition scale residual) depth scaledJoint command state
  rw [scaledTransition, Matrix.smul_mulVec,
    quadraticEnergy_state_smul] at contraction
  have denominator_pos : 0 < 2 * scale ^ 2 := by positivity
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ denominator_pos).2
  nlinarith

omit [Fintype Command] [DecidableEq Command] in
/-- Applying one scalar-shifted command is the sum of its scalar state
component and residual response. -/
theorem scalarShiftedTransition_mulVec
    (coefficient : Command → ℝ)
    (residual : Command → Matrix Index Index ℝ)
    (command : Command) (state : Index → ℝ) :
    scalarShiftedTransition coefficient residual command *ᵥ state =
      coefficient command • state + residual command *ᵥ state := by
  simp [scalarShiftedTransition, Matrix.add_mulVec, Matrix.smul_mulVec]

/-- A scalar contraction plus a jointly nilpotent routed residual has one
explicit common strict quadratic Lyapunov metric. -/
noncomputable def scalarShiftedJointNilpotentCommonLyapunov
    (coefficient : Command → ℝ)
    (residual : Command → Matrix Index Index ℝ)
    (depth : ℕ)
    (jointlyNilpotent : JointlyNilpotentAt residual (depth + 2))
    (scale radius : ℝ)
    (scale_pos : 0 < scale)
    (coefficient_bound : ∀ command, |coefficient command| ≤ radius)
    (strict_rate : 2 * radius ^ 2 + 1 / scale ^ 2 < 1) :
    CommonQuadraticLyapunov (scalarShiftedTransition coefficient residual) where
  metric := jointNilpotentMetric (scaledTransition scale residual) (depth + 1)
  rate := 2 * radius ^ 2 + 1 / scale ^ 2
  rate_nonneg := by positivity
  rate_lt_one := strict_rate
  energy_nonneg := jointNilpotentMetric_energy_nonneg
    (scaledTransition scale residual) (depth + 1)
  contracts := by
    intro command state
    let metric := jointNilpotentMetric
      (scaledTransition scale residual) (depth + 1)
    have metric_nonneg (value : Index → ℝ) :
        0 ≤ quadraticEnergy metric value :=
      jointNilpotentMetric_energy_nonneg
        (scaledTransition scale residual) (depth + 1) value
    have split_bound := quadraticEnergy_add_le_two metric metric_nonneg
      (coefficient command • state) (residual command *ᵥ state)
    have coefficient_energy := quadraticEnergy_state_smul
      metric (coefficient command) state
    have residual_energy := jointlyNilpotent_residual_energy_le
      residual depth jointlyNilpotent scale scale_pos command state
    have coefficient_interval := abs_le.mp (coefficient_bound command)
    have coefficient_sq_le : coefficient command ^ 2 ≤ radius ^ 2 := by
      nlinarith
    have coefficient_term_le :
        coefficient command ^ 2 * quadraticEnergy metric state ≤
          radius ^ 2 * quadraticEnergy metric state :=
      mul_le_mul_of_nonneg_right coefficient_sq_le (metric_nonneg state)
    have residual_rate_identity :
        2 * (1 / (2 * scale ^ 2)) = 1 / scale ^ 2 := by
      field_simp
    rw [scalarShiftedTransition_mulVec]
    rw [coefficient_energy] at split_bound
    rw [residual_rate_identity.symm]
    nlinarith

/-! ## Positive and negative fixtures -/

/-- Persistent quarter-contraction added to each positive residual fixture. -/
noncomputable def quarterCoefficient (_ : Bool) : ℝ := 1 / 4

/-- A concrete nonnilpotent routed family certified by the scalar-shift
construction. -/
noncomputable def quarterShiftedNilpotentABCommonLyapunov :
    CommonQuadraticLyapunov
      (scalarShiftedTransition quarterCoefficient
        (twoCommandTransition commutingNilpotentA commutingNilpotentB)) :=
  scalarShiftedJointNilpotentCommonLyapunov quarterCoefficient
    (twoCommandTransition commutingNilpotentA commutingNilpotentB)
    1 commutingNilpotentAB_jointlyNilpotentAt_three 4 (1 / 4)
    (by norm_num)
    (fun command => by cases command <;> norm_num [quarterCoefficient])
    (by norm_num)

/-- The first shifted fixture command. -/
noncomputable def quarterShiftedA : Matrix (Fin 2) (Fin 2) ℝ :=
  scalarShiftedTransition quarterCoefficient
    (twoCommandTransition commutingNilpotentA commutingNilpotentB) false

theorem quarterShiftedA_pow_zero_zero (exponent : ℕ) :
    (quarterShiftedA ^ exponent) 0 0 = (1 / 4 : ℝ) ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      have diagonal : quarterShiftedA 0 0 = (1 / 4 : ℝ) := by
        norm_num [quarterShiftedA, scalarShiftedTransition,
          quarterCoefficient, twoCommandTransition, commutingNilpotentA]
      have belowDiagonal : quarterShiftedA 1 0 = 0 := by
        norm_num [quarterShiftedA, scalarShiftedTransition,
          quarterCoefficient, twoCommandTransition, commutingNilpotentA]
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, diagonal,
        belowDiagonal, mul_zero, add_zero, ih, pow_succ]

/-- The positive shifted fixture is genuinely outside the nilpotent family. -/
theorem quarterShiftedA_not_nilpotent (exponent : ℕ) :
    quarterShiftedA ^ exponent ≠ 0 := by
  intro power_zero
  have entry_zero := congr_fun (congr_fun power_zero 0) 0
  rw [quarterShiftedA_pow_zero_zero] at entry_zero
  exact (pow_ne_zero exponent (by norm_num : (1 / 4 : ℝ) ≠ 0)) entry_zero

/-- The strict-rate gate is substantive: unit scalar radius and unit residual
scale cannot satisfy it. -/
theorem unitRadius_unitScale_fails_strictRate :
    ¬ (2 * (1 : ℝ) ^ 2 + 1 / (1 : ℝ) ^ 2 < 1) := by
  norm_num

#print axioms runLinearSchedule_scaledTransition
#print axioms JointlyNilpotentAt.scaledTransition
#print axioms quadraticEnergy_state_smul
#print axioms quadraticEnergy_add_le_two
#print axioms jointlyNilpotent_residual_energy_le
#print axioms scalarShiftedJointNilpotentCommonLyapunov
#print axioms quarterShiftedNilpotentABCommonLyapunov
#print axioms quarterShiftedA_not_nilpotent
#print axioms unitRadius_unitScale_fails_strictRate

end ScalarShift

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
