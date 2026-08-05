import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Residual-energy stability and task-descent boundaries

Gradient flow for a composite energy always decreases that composite energy.
It does not follow merely from positivity of the added residual energy that
the composite flow decreases faster than task-only gradient flow, or even
that it decreases the task loss.

This file isolates the exact missing conditions.  The instantaneous
composite-energy rate is no larger than the task-only rate exactly when the
residual gradient satisfies a cross-term inequality.  Task loss decreases
along the composite flow exactly when the task gradient is nonnegatively
aligned with the composite gradient.

Two positive-definite quadratic fixtures show that positivity and smoothness
of the component energies do not imply either condition.  In the first,
adding a sum-of-squared-residuals energy makes the instantaneous composite
rate strictly slower.  In the second, the negative composite-gradient step
strictly increases the task loss.  Both component energies have the same
unique minimizer.

Source correspondence: Mali, Salvatori, and Ororbia, *Tight Stability,
Convergence, and Robustness Bounds for Predictive Coding Networks*,
arXiv:2410.04708, Theorems 3.2--3.6 and especially the comparison step in
Appendix C.4.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

namespace ResidualEnergyStabilityBoundary

open scoped InnerProductSpace

noncomputable section

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-! ## Exact Hilbert-space comparison -/

/-- The cross term omitted by a bare appeal to an additional residual
energy. -/
theorem compositeGradient_norm_sq_sub_taskGradient_norm_sq
    (taskGradient residualGradient : Parameter) :
    ‖taskGradient + residualGradient‖ ^ 2 - ‖taskGradient‖ ^ 2 =
      2 * ⟪taskGradient, residualGradient⟫_ℝ +
        ‖residualGradient‖ ^ 2 := by
  rw [norm_add_sq_real]
  ring

/-- The exact condition under which the composite gradient has at least the
task gradient's norm. -/
theorem compositeGradient_norm_sq_ge_iff
    (taskGradient residualGradient : Parameter) :
    ‖taskGradient‖ ^ 2 ≤ ‖taskGradient + residualGradient‖ ^ 2 ↔
      0 ≤ 2 * ⟪taskGradient, residualGradient⟫_ℝ +
        ‖residualGradient‖ ^ 2 := by
  have identity :=
    compositeGradient_norm_sq_sub_taskGradient_norm_sq
      taskGradient residualGradient
  constructor <;> intro comparison <;> linarith

/-- Instantaneous Lyapunov rate under a negative-gradient flow. -/
def gradientFlowEnergyRate (gradient : Parameter) : ℝ :=
  -(‖gradient‖ ^ 2)

/-- Comparing the two instantaneous energy rates requires exactly the same
cross-term condition. -/
theorem compositeEnergyRate_le_taskEnergyRate_iff
    (taskGradient residualGradient : Parameter) :
    gradientFlowEnergyRate (taskGradient + residualGradient) ≤
        gradientFlowEnergyRate taskGradient ↔
      0 ≤ 2 * ⟪taskGradient, residualGradient⟫_ℝ +
        ‖residualGradient‖ ^ 2 := by
  rw [gradientFlowEnergyRate, gradientFlowEnergyRate]
  constructor
  · intro rate
    apply (compositeGradient_norm_sq_ge_iff
      taskGradient residualGradient).mp
    linarith
  · intro cross
    have normComparison :=
      (compositeGradient_norm_sq_ge_iff
        taskGradient residualGradient).mpr cross
    linarith

/-- The task-loss rate along the composite negative-gradient flow. -/
def taskRateAlongCompositeFlow
    (taskGradient residualGradient : Parameter) : ℝ :=
  -⟪taskGradient, taskGradient + residualGradient⟫_ℝ

/-- Task descent along the composite flow is an alignment condition, not a
consequence of nonnegativity of either energy value. -/
theorem taskRateAlongCompositeFlow_nonpos_iff
    (taskGradient residualGradient : Parameter) :
    taskRateAlongCompositeFlow taskGradient residualGradient ≤ 0 ↔
      0 ≤ ⟪taskGradient, taskGradient + residualGradient⟫_ℝ := by
  simp only [taskRateAlongCompositeFlow]
  exact neg_nonpos

/-- Nonnegative task--residual gradient alignment is a sufficient repaired
premise for both rate comparisons. -/
theorem alignedResidual_licenses_both_rate_comparisons
    (taskGradient residualGradient : Parameter)
    (aligned : 0 ≤ ⟪taskGradient, residualGradient⟫_ℝ) :
    gradientFlowEnergyRate (taskGradient + residualGradient) ≤
        gradientFlowEnergyRate taskGradient ∧
      taskRateAlongCompositeFlow taskGradient residualGradient ≤ 0 := by
  constructor
  · apply (compositeEnergyRate_le_taskEnergyRate_iff
      taskGradient residualGradient).mpr
    nlinarith [sq_nonneg ‖residualGradient‖]
  · apply (taskRateAlongCompositeFlow_nonpos_iff
      taskGradient residualGradient).mpr
    rw [inner_add_right, real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖taskGradient‖]

/-! ## Exact two-coordinate quadratic witnesses -/

abbrev Plane := ℝ × ℝ

def dot2 (left right : Plane) : ℝ :=
  left.1 * right.1 + left.2 * right.2

def normSq2 (point : Plane) : ℝ :=
  point.1 ^ 2 + point.2 ^ 2

def add2 (left right : Plane) : Plane :=
  (left.1 + right.1, left.2 + right.2)

def step2 (point direction : Plane) (rate : ℝ) : Plane :=
  (point.1 - rate * direction.1,
    point.2 - rate * direction.2)

/-! ### A positive residual energy can slow the composite energy rate -/

def slowTaskEnergy (point : Plane) : ℝ :=
  (point.1 ^ 2 + 4 * point.2 ^ 2) / 2

def slowTaskGradient (point : Plane) : Plane :=
  (point.1, 4 * point.2)

/-- A sum of two squared linear residuals. -/
def slowResidualEnergy (point : Plane) : ℝ :=
  ((point.1 - point.2) ^ 2 +
    (point.1 - 2 * point.2) ^ 2) / 2

def slowResidualGradient (point : Plane) : Plane :=
  (2 * point.1 - 3 * point.2,
    -3 * point.1 + 5 * point.2)

def slowCompositeGradient (point : Plane) : Plane :=
  add2 (slowTaskGradient point) (slowResidualGradient point)

/-- Exact finite increment establishes the declared task gradient without
appealing to an informal derivative calculation. -/
theorem slowTaskEnergy_step_expansion
    (point direction : Plane) (rate : ℝ) :
    slowTaskEnergy (step2 point direction rate) -
        slowTaskEnergy point =
      -rate * dot2 (slowTaskGradient point) direction +
        rate ^ 2 / 2 * (direction.1 ^ 2 + 4 * direction.2 ^ 2) := by
  simp [slowTaskEnergy, step2, dot2, slowTaskGradient]
  ring

/-- Exact finite increment for the squared-residual energy. -/
theorem slowResidualEnergy_step_expansion
    (point direction : Plane) (rate : ℝ) :
    slowResidualEnergy (step2 point direction rate) -
        slowResidualEnergy point =
      -rate * dot2 (slowResidualGradient point) direction +
        rate ^ 2 / 2 *
          ((direction.1 - direction.2) ^ 2 +
            (direction.1 - 2 * direction.2) ^ 2) := by
  simp [slowResidualEnergy, step2, dot2, slowResidualGradient]
  ring

theorem slowTaskEnergy_nonneg (point : Plane) :
    0 ≤ slowTaskEnergy point := by
  simp [slowTaskEnergy]
  positivity

theorem slowTaskEnergy_eq_zero_iff (point : Plane) :
    slowTaskEnergy point = 0 ↔ point = (0, 0) := by
  constructor
  · intro energy_zero
    have first_sq : 0 ≤ point.1 ^ 2 := sq_nonneg _
    have second_sq : 0 ≤ point.2 ^ 2 := sq_nonneg _
    have first_zero : point.1 = 0 := by
      have : point.1 ^ 2 = 0 := by
        simp [slowTaskEnergy] at energy_zero
        nlinarith
      nlinarith
    have second_zero : point.2 = 0 := by
      have : point.2 ^ 2 = 0 := by
        simp [slowTaskEnergy] at energy_zero
        nlinarith
      nlinarith
    exact Prod.ext first_zero second_zero
  · rintro rfl
    norm_num [slowTaskEnergy]

theorem slowResidualEnergy_nonneg (point : Plane) :
    0 ≤ slowResidualEnergy point := by
  simp [slowResidualEnergy]
  positivity

theorem slowResidualEnergy_eq_zero_iff (point : Plane) :
    slowResidualEnergy point = 0 ↔ point = (0, 0) := by
  constructor
  · intro energy_zero
    have first_sq : 0 ≤ (point.1 - point.2) ^ 2 := sq_nonneg _
    have second_sq : 0 ≤ (point.1 - 2 * point.2) ^ 2 := sq_nonneg _
    have first_zero : point.1 - point.2 = 0 := by
      have : (point.1 - point.2) ^ 2 = 0 := by
        simp [slowResidualEnergy] at energy_zero
        nlinarith
      nlinarith
    have second_zero : point.1 - 2 * point.2 = 0 := by
      have : (point.1 - 2 * point.2) ^ 2 = 0 := by
        simp [slowResidualEnergy] at energy_zero
        nlinarith
      nlinarith
    have second_coordinate : point.2 = 0 := by linarith
    have first_coordinate : point.1 = 0 := by linarith
    exact Prod.ext first_coordinate second_coordinate
  · rintro rfl
    norm_num [slowResidualEnergy]

/-- Both positive-definite energies have the same unique minimizer, yet the
additional residual gradient makes the claimed instantaneous rate comparison
strictly worse. -/
theorem positiveResidual_can_slow_composite_energy_rate :
    let point : Plane := (2, 1)
    0 < slowTaskEnergy point ∧
      0 < slowResidualEnergy point ∧
      normSq2 (slowCompositeGradient point) <
        normSq2 (slowTaskGradient point) := by
  norm_num [slowTaskEnergy, slowResidualEnergy, slowCompositeGradient,
    slowTaskGradient, slowResidualGradient, add2, normSq2]

/-! ### A positive residual energy can make the task ascend -/

def ascentTaskEnergy (point : Plane) : ℝ :=
  (point.1 ^ 2 + 6 * point.2 ^ 2) / 2

def ascentTaskGradient (point : Plane) : Plane :=
  (point.1, 6 * point.2)

/-- Another positive-definite sum of squared linear residuals. -/
def ascentResidualEnergy (point : Plane) : ℝ :=
  ((2 * point.1 - 3 * point.2) ^ 2 +
    (point.1 - point.2) ^ 2) / 2

def ascentResidualGradient (point : Plane) : Plane :=
  (5 * point.1 - 7 * point.2,
    -7 * point.1 + 10 * point.2)

def ascentCompositeGradient (point : Plane) : Plane :=
  add2 (ascentTaskGradient point) (ascentResidualGradient point)

theorem ascentTaskEnergy_step_expansion
    (point direction : Plane) (rate : ℝ) :
    ascentTaskEnergy (step2 point direction rate) -
        ascentTaskEnergy point =
      -rate * dot2 (ascentTaskGradient point) direction +
        rate ^ 2 / 2 * (direction.1 ^ 2 + 6 * direction.2 ^ 2) := by
  simp [ascentTaskEnergy, step2, dot2, ascentTaskGradient]
  ring

theorem ascentResidualEnergy_nonneg (point : Plane) :
    0 ≤ ascentResidualEnergy point := by
  simp [ascentResidualEnergy]
  positivity

theorem ascentResidualEnergy_eq_zero_iff (point : Plane) :
    ascentResidualEnergy point = 0 ↔ point = (0, 0) := by
  constructor
  · intro energy_zero
    have first_sq : 0 ≤ (2 * point.1 - 3 * point.2) ^ 2 := sq_nonneg _
    have second_sq : 0 ≤ (point.1 - point.2) ^ 2 := sq_nonneg _
    have first_zero : 2 * point.1 - 3 * point.2 = 0 := by
      have : (2 * point.1 - 3 * point.2) ^ 2 = 0 := by
        simp [ascentResidualEnergy] at energy_zero
        nlinarith
      nlinarith
    have second_zero : point.1 - point.2 = 0 := by
      have : (point.1 - point.2) ^ 2 = 0 := by
        simp [ascentResidualEnergy] at energy_zero
        nlinarith
      nlinarith
    have second_coordinate : point.2 = 0 := by linarith
    have first_coordinate : point.1 = 0 := by linarith
    exact Prod.ext first_coordinate second_coordinate
  · rintro rfl
    norm_num [ascentResidualEnergy]

/-- At this point the task gradient and composite gradient have negative
inner product, despite both component energies being positive definite. -/
theorem positiveResidual_can_reverse_task_alignment :
    let point : Plane := (4, 1)
    0 < ascentTaskEnergy point ∧
      0 < ascentResidualEnergy point ∧
      dot2 (ascentTaskGradient point)
        (ascentCompositeGradient point) < 0 := by
  norm_num [ascentTaskEnergy, ascentResidualEnergy,
    ascentTaskGradient, ascentResidualGradient, ascentCompositeGradient,
    add2, dot2]

/-- The alignment failure is visible in a finite rational step: following
the composite negative gradient strictly raises the task loss. -/
theorem positiveResidual_composite_step_can_raise_task :
    let point : Plane := (4, 1)
    ascentTaskEnergy point <
      ascentTaskEnergy
        (step2 point (ascentCompositeGradient point) (1 / 100)) := by
  norm_num [ascentTaskEnergy, ascentCompositeGradient,
    ascentTaskGradient, ascentResidualGradient, add2, step2]

/-! ### A strict global minimum need not be the only stationary point -/

/-- A smooth positive-definite scalar energy with a unique zero but an
additional stationary point. -/
def stationaryBoundaryEnergy (state : ℝ) : ℝ :=
  state ^ 2 * (state - 1) ^ 2 + state ^ 2 / 8

def stationaryBoundaryGradient (state : ℝ) : ℝ :=
  2 * state * (state - 1) * (2 * state - 1) + state / 4

theorem stationaryBoundaryEnergy_nonneg (state : ℝ) :
    0 ≤ stationaryBoundaryEnergy state := by
  simp [stationaryBoundaryEnergy]
  positivity

theorem stationaryBoundaryEnergy_eq_zero_iff (state : ℝ) :
    stationaryBoundaryEnergy state = 0 ↔ state = 0 := by
  constructor
  · intro energy_zero
    have product_nonneg :
        0 ≤ state ^ 2 * (state - 1) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have square_nonneg : 0 ≤ state ^ 2 := sq_nonneg _
    have square_zero : state ^ 2 = 0 := by
      simp [stationaryBoundaryEnergy] at energy_zero
      nlinarith
    nlinarith
  · rintro rfl
    norm_num [stationaryBoundaryEnergy]

/-- The declared gradient is certified by an exact finite increment, with
all higher-order terms exposed. -/
theorem stationaryBoundaryEnergy_step_expansion
    (state direction rate : ℝ) :
    stationaryBoundaryEnergy (state - rate * direction) -
        stationaryBoundaryEnergy state =
      -rate * stationaryBoundaryGradient state * direction +
        rate ^ 2 *
          (direction ^ 2 *
            (6 * state ^ 2 - 6 * state + 9 / 8) -
            4 * rate * state * direction ^ 3 +
            2 * rate * direction ^ 3 +
            rate ^ 2 * direction ^ 4) := by
  simp [stationaryBoundaryEnergy, stationaryBoundaryGradient]
  ring

/-- Positive definiteness and a strict unique global minimum do not imply
that the Lyapunov derivative vanishes only at that minimum. -/
theorem strictMinimum_does_not_exclude_other_stationary_points :
    stationaryBoundaryGradient (3 / 4) = 0 ∧
      0 < stationaryBoundaryEnergy (3 / 4) := by
  norm_num [stationaryBoundaryGradient, stationaryBoundaryEnergy]

#print axioms compositeEnergyRate_le_taskEnergyRate_iff
#print axioms taskRateAlongCompositeFlow_nonpos_iff
#print axioms alignedResidual_licenses_both_rate_comparisons
#print axioms positiveResidual_can_slow_composite_energy_rate
#print axioms positiveResidual_can_reverse_task_alignment
#print axioms positiveResidual_composite_step_can_raise_task
#print axioms strictMinimum_does_not_exclude_other_stationary_points

end

end ResidualEnergyStabilityBoundary

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
