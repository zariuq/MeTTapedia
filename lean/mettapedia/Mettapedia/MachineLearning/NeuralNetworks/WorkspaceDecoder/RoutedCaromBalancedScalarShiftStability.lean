import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromScalarShiftStability

/-!
# Routed CAROM: balanced scalar-shift stability

The first scalar-shift certificate used the symmetric estimate
`E(u + v) ≤ 2 E(u) + 2 E(v)`.  That estimate is useful for small scalar
parts, but it cannot reach scalar contractions close to the unit circle.

This file replaces the fixed factor two by a positive balance parameter.  The
resulting Young-type estimate lets the scalar contribution stay arbitrarily
close to its exact squared modulus while the jointly nilpotent residual is
suppressed by scaling its recursive word metric.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function
open scoped Matrix BigOperators

namespace RoutedCarom

universe uCommand uIndex

section BalancedScalarShift

variable {Command : Type uCommand} [Fintype Command] [DecidableEq Command]
variable {Index : Type uIndex} [Fintype Index] [DecidableEq Index]

omit [Fintype Command] [DecidableEq Command] [DecidableEq Index] in
/-- A tunable two-term upper bound for every nonnegative quadratic energy.
The balance parameter controls how much of the cross term is charged to each
summand. -/
theorem quadraticEnergy_add_le_balanced
    (metric : Matrix Index Index ℝ)
    (energy_nonneg : ∀ state, 0 ≤ quadraticEnergy metric state)
    (balance : ℝ) (balance_pos : 0 < balance)
    (first second : Index → ℝ) :
    quadraticEnergy metric (first + second) ≤
      (1 + balance) * quadraticEnergy metric first +
        (1 + 1 / balance) * quadraticEnergy metric second := by
  have scaledDifference_nonneg :=
    energy_nonneg (balance • first - second)
  have cancellationIdentity :
      quadraticEnergy metric (balance • first - second) +
          balance * quadraticEnergy metric (first + second) =
        (balance ^ 2 + balance) * quadraticEnergy metric first +
          (1 + balance) * quadraticEnergy metric second := by
    simp only [quadraticEnergy, Matrix.mulVec_sub, Matrix.mulVec_add,
      Matrix.mulVec_smul,
      sub_dotProduct, add_dotProduct, dotProduct_sub, dotProduct_add,
      smul_dotProduct, dotProduct_smul]
    ring
  have multipliedBound :
      balance * quadraticEnergy metric (first + second) ≤
        (balance ^ 2 + balance) * quadraticEnergy metric first +
          (1 + balance) * quadraticEnergy metric second := by
    linarith
  have weightedIdentity :
      balance *
          ((1 + balance) * quadraticEnergy metric first +
            (1 + 1 / balance) * quadraticEnergy metric second) =
        (balance ^ 2 + balance) * quadraticEnergy metric first +
          (1 + balance) * quadraticEnergy metric second := by
    field_simp [ne_of_gt balance_pos]
    ring
  have multipliedGoal :
      quadraticEnergy metric (first + second) * balance ≤
        ((1 + balance) * quadraticEnergy metric first +
          (1 + 1 / balance) * quadraticEnergy metric second) * balance := by
    calc
      quadraticEnergy metric (first + second) * balance =
          balance * quadraticEnergy metric (first + second) := mul_comm _ _
      _ ≤ (balance ^ 2 + balance) * quadraticEnergy metric first +
          (1 + balance) * quadraticEnergy metric second := multipliedBound
      _ = balance *
          ((1 + balance) * quadraticEnergy metric first +
            (1 + 1 / balance) * quadraticEnergy metric second) :=
        weightedIdentity.symm
      _ = ((1 + balance) * quadraticEnergy metric first +
          (1 + 1 / balance) * quadraticEnergy metric second) * balance :=
        mul_comm _ _
  exact (mul_le_mul_iff_left₀ balance_pos).mp multipliedGoal

/-- A scalar contraction plus a jointly nilpotent routed residual has a
balanced common strict quadratic Lyapunov metric.  Unlike the fixed-factor
certificate, its scalar contribution can approach the exact radius squared. -/
noncomputable def balancedScalarShiftedJointNilpotentCommonLyapunov
    (coefficient : Command → ℝ)
    (residual : Command → Matrix Index Index ℝ)
    (depth : ℕ)
    (jointlyNilpotent : JointlyNilpotentAt residual (depth + 2))
    (scale radius balance : ℝ)
    (scale_pos : 0 < scale)
    (balance_pos : 0 < balance)
    (coefficient_bound : ∀ command, |coefficient command| ≤ radius)
    (strict_rate :
      (1 + balance) * radius ^ 2 +
          (1 + 1 / balance) / (2 * scale ^ 2) < 1) :
    CommonQuadraticLyapunov (scalarShiftedTransition coefficient residual) where
  metric := jointNilpotentMetric (scaledTransition scale residual) (depth + 1)
  rate :=
    (1 + balance) * radius ^ 2 +
      (1 + 1 / balance) / (2 * scale ^ 2)
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
    have split_bound := quadraticEnergy_add_le_balanced metric metric_nonneg
      balance balance_pos (coefficient command • state)
        (residual command *ᵥ state)
    have coefficient_energy := quadraticEnergy_state_smul
      metric (coefficient command) state
    have residual_energy := jointlyNilpotent_residual_energy_le
      residual depth jointlyNilpotent scale scale_pos command state
    have coefficient_interval := abs_le.mp (coefficient_bound command)
    have coefficient_sq_le : coefficient command ^ 2 ≤ radius ^ 2 := by
      nlinarith
    have coefficient_term_le :
        (1 + balance) *
            (coefficient command ^ 2 * quadraticEnergy metric state) ≤
          (1 + balance) *
            (radius ^ 2 * quadraticEnergy metric state) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right coefficient_sq_le (metric_nonneg state))
        (by positivity)
    have residual_term_le :
        (1 + 1 / balance) *
            quadraticEnergy metric (residual command *ᵥ state) ≤
          (1 + 1 / balance) *
            ((1 / (2 * scale ^ 2)) * quadraticEnergy metric state) := by
      exact mul_le_mul_of_nonneg_left residual_energy (by positivity)
    rw [scalarShiftedTransition_mulVec]
    rw [coefficient_energy] at split_bound
    calc
      quadraticEnergy metric
          (coefficient command • state + residual command *ᵥ state) ≤
          (1 + balance) *
              (coefficient command ^ 2 * quadraticEnergy metric state) +
            (1 + 1 / balance) *
              quadraticEnergy metric (residual command *ᵥ state) := split_bound
      _ ≤
          (1 + balance) *
              (radius ^ 2 * quadraticEnergy metric state) +
            (1 + 1 / balance) *
              ((1 / (2 * scale ^ 2)) * quadraticEnergy metric state) :=
        add_le_add coefficient_term_le residual_term_le
      _ =
          ((1 + balance) * radius ^ 2 +
              (1 + 1 / balance) / (2 * scale ^ 2)) *
            quadraticEnergy metric state := by ring

/-- Every nonnegative scalar radius strictly below one admits a balance and a
residual scale satisfying the balanced strict-rate gate.  Thus the real
scalar-plus-jointly-nilpotent construction needs no margin beyond strict
unit-disk scalar stability. -/
theorem exists_balance_scale_strict_rate
    (radius : ℝ) (radius_nonneg : 0 ≤ radius) (radius_lt_one : radius < 1) :
    ∃ balance scale : ℝ,
      0 < balance ∧ 0 < scale ∧
        (1 + balance) * radius ^ 2 +
            (1 + 1 / balance) / (2 * scale ^ 2) < 1 := by
  have radius_sq_lt_one : radius ^ 2 < 1 := by
    have factor_pos : 0 < (1 - radius) * (1 + radius) :=
      mul_pos (sub_pos.mpr radius_lt_one) (by linarith)
    nlinarith
  let balance : ℝ := (1 - radius ^ 2) / 2
  have balance_pos : 0 < balance := by
    dsimp [balance]
    linarith
  let scalarPart : ℝ := (1 + balance) * radius ^ 2
  have scalarPart_lt_one : scalarPart < 1 := by
    have secondFactor_pos : 0 < 1 - radius ^ 2 / 2 := by linarith
    have product_pos :
        0 < (1 - radius ^ 2) * (1 - radius ^ 2 / 2) :=
      mul_pos (sub_pos.mpr radius_sq_lt_one) secondFactor_pos
    dsimp [scalarPart, balance]
    nlinarith
  let margin : ℝ := 1 - scalarPart
  have margin_pos : 0 < margin := by
    dsimp [margin]
    linarith
  let numerator : ℝ := 1 + 1 / balance
  have numerator_pos : 0 < numerator := by
    dsimp [numerator]
    positivity
  let target : ℝ := numerator / (2 * margin)
  have target_pos : 0 < target := by
    dsimp [target]
    positivity
  let scale : ℝ := target + 1
  have scale_pos : 0 < scale := by
    dsimp [scale]
    linarith
  have target_lt_scale_sq : target < scale ^ 2 := by
    dsimp [scale]
    nlinarith [sq_nonneg target]
  have numerator_identity : numerator = target * (2 * margin) := by
    dsimp [target]
    field_simp [ne_of_gt margin_pos]
  have residual_lt_margin :
      numerator / (2 * scale ^ 2) < margin := by
    rw [div_lt_iff₀ (by positivity : 0 < 2 * scale ^ 2)]
    rw [numerator_identity]
    nlinarith
  refine ⟨balance, scale, balance_pos, scale_pos, ?_⟩
  change scalarPart + numerator / (2 * scale ^ 2) < 1
  dsimp [margin] at residual_lt_margin
  linarith

/-- Existence form of the balanced common-metric theorem: every finite
jointly nilpotent residual family added to real scalar contractions of strict
radius below one has a common strict quadratic Lyapunov certificate. -/
theorem exists_balancedScalarShiftedJointNilpotentCommonLyapunov
    (coefficient : Command → ℝ)
    (residual : Command → Matrix Index Index ℝ)
    (depth : ℕ)
    (jointlyNilpotent : JointlyNilpotentAt residual (depth + 2))
    (radius : ℝ) (radius_nonneg : 0 ≤ radius) (radius_lt_one : radius < 1)
    (coefficient_bound : ∀ command, |coefficient command| ≤ radius) :
    Nonempty
      (CommonQuadraticLyapunov
        (scalarShiftedTransition coefficient residual)) := by
  obtain ⟨balance, scale, balance_pos, scale_pos, strict_rate⟩ :=
    exists_balance_scale_strict_rate radius radius_nonneg radius_lt_one
  exact ⟨balancedScalarShiftedJointNilpotentCommonLyapunov
    coefficient residual depth jointlyNilpotent scale radius balance
    scale_pos balance_pos coefficient_bound strict_rate⟩

/-! ## Positive and negative fixtures -/

/-- A scalar coefficient close to the unit-circle boundary. -/
noncomputable def nineTenthsCoefficient (_ : Bool) : ℝ := 9 / 10

/-- The balanced certificate handles a scalar radius of `9/10`, well beyond
the range of the earlier fixed-factor estimate. -/
noncomputable def nineTenthsShiftedNilpotentABCommonLyapunov :
    CommonQuadraticLyapunov
      (scalarShiftedTransition nineTenthsCoefficient
        (twoCommandTransition commutingNilpotentA commutingNilpotentB)) :=
  balancedScalarShiftedJointNilpotentCommonLyapunov nineTenthsCoefficient
    (twoCommandTransition commutingNilpotentA commutingNilpotentB)
    1 commutingNilpotentAB_jointlyNilpotentAt_three 20 (9 / 10) (1 / 10)
    (by norm_num)
    (by norm_num)
    (fun command => by cases command <;> norm_num [nineTenthsCoefficient])
    (by norm_num)

/-- The old fixed-factor bound cannot certify the same radius, even at the
larger residual scale used by the balanced positive fixture. -/
theorem nineTenths_fixedFactor_rate_fails :
    ¬ (2 * (9 / 10 : ℝ) ^ 2 + 1 / (20 : ℝ) ^ 2 < 1) := by
  norm_num

/-- No positive balance and residual scale can turn unit scalar radius into a
strict contraction under the balanced rate formula. -/
theorem unitRadius_balanced_rate_fails
    (scale balance : ℝ) (scale_pos : 0 < scale) (balance_pos : 0 < balance) :
    ¬ ((1 + balance) * (1 : ℝ) ^ 2 +
        (1 + 1 / balance) / (2 * scale ^ 2) < 1) := by
  have residualTermNonneg :
      0 ≤ (1 + 1 / balance) / (2 * scale ^ 2) := by positivity
  intro strictRate
  have unitRateLowerBound :
      1 ≤ (1 + balance) * (1 : ℝ) ^ 2 +
        (1 + 1 / balance) / (2 * scale ^ 2) := by
    norm_num
    linarith
  exact (not_lt_of_ge unitRateLowerBound) strictRate

#print axioms quadraticEnergy_add_le_balanced
#print axioms balancedScalarShiftedJointNilpotentCommonLyapunov
#print axioms exists_balance_scale_strict_rate
#print axioms exists_balancedScalarShiftedJointNilpotentCommonLyapunov
#print axioms nineTenthsShiftedNilpotentABCommonLyapunov
#print axioms nineTenths_fixedFactor_rate_fails
#print axioms unitRadius_balanced_rate_fails

end BalancedScalarShift

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
