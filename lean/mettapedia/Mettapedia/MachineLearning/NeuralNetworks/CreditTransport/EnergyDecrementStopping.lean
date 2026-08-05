import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization

/-!
# Certified energy-decrement stopping

FabricPC proposes adaptive settling from a measured per-step energy decrement.
A small decrement is a fixed-point certificate only when the decrement is
quantitatively tied to the solver residual.  This file states that missing
premise explicitly and composes it with the existing contraction-residual
bound.

If one step decreases energy by at least a positive coefficient times the
squared solver residual, then a small observed decrement bounds a scaled
squared distance to the fixed point.  A strongly convex scalar quadratic gives
the sharp negative boundary: an arbitrarily slow but contractive gradient step
has a tiny raw energy decrement while remaining unit distance from its fixed
point.  The contraction-normalized residual test correctly rejects that state.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace EnergyDecrementStopping

open AmortizedInitialization

variable {State : Type*} [NormedAddCommGroup State]

/-- A pointwise bridge from energy decrease to the observable solver residual.
The coefficient records the step-size and curvature dependence which a raw
energy-decrement tolerance omits. -/
structure ResidualDecreaseCertificate
    (energy : State → ℝ)
    (solver : State → State)
    (state : State)
    (coefficient : ℝ) : Prop where
  coefficient_pos : 0 < coefficient
  residual_sq_le_decrease :
    coefficient * ‖state - solver state‖ ^ 2 ≤
      energy state - energy (solver state)

/-- A certified small energy decrement bounds the squared solver residual. -/
theorem residual_sq_le_tolerance_div
    {energy : State → ℝ}
    {solver : State → State}
    {state : State}
    {coefficient tolerance : ℝ}
    (certificate :
      ResidualDecreaseCertificate energy solver state coefficient)
    (decrement_le :
      energy state - energy (solver state) ≤ tolerance) :
    ‖state - solver state‖ ^ 2 ≤ tolerance / coefficient := by
  apply (le_div_iff₀ certificate.coefficient_pos).2
  simpa [mul_comm] using
    certificate.residual_sq_le_decrease.trans decrement_le

/-- The energy-decrement certificate composes with contraction: the observable
tolerance controls fixed-point distance after paying both the decrease
coefficient and the square of the contraction margin. -/
theorem fixedPoint_scaled_sq_le_tolerance
    {energy : State → ℝ}
    {solver : State → State}
    {target state : State}
    {coefficient tolerance : ℝ}
    (contraction : ContractionCertificate solver)
    (target_fixed : IsFixedPoint solver target)
    (decrease :
      ResidualDecreaseCertificate energy solver state coefficient)
    (decrement_le :
      energy state - energy (solver state) ≤ tolerance) :
    coefficient * (1 - contraction.factor) ^ 2 *
        ‖state - target‖ ^ 2 ≤
      tolerance := by
  have margin_pos : 0 < 1 - contraction.factor := by
    linarith [contraction.factor_lt_one]
  have distance_bound :=
    fixedPoint_distance_le_residual_div
      contraction target state target_fixed
  have scaled_distance :
      (1 - contraction.factor) * ‖state - target‖ ≤
        ‖state - solver state‖ := by
    simpa [mul_comm] using
      (le_div_iff₀ margin_pos).mp distance_bound
  have scaled_nonnegative :
      0 ≤ (1 - contraction.factor) * ‖state - target‖ :=
    mul_nonneg margin_pos.le (norm_nonneg _)
  have residual_nonnegative :
      0 ≤ ‖state - solver state‖ :=
    norm_nonneg _
  have squared_distance :
      ((1 - contraction.factor) * ‖state - target‖) ^ 2 ≤
        ‖state - solver state‖ ^ 2 :=
    (sq_le_sq₀ scaled_nonnegative residual_nonnegative).2 scaled_distance
  have residual_budget :
      coefficient * ‖state - solver state‖ ^ 2 ≤ tolerance :=
    decrease.residual_sq_le_decrease.trans decrement_le
  nlinarith [decrease.coefficient_pos]

/-! ## A slow-step counterexample to raw decrement tolerances -/

noncomputable def slowRate : ℝ :=
  1 / 1000000

noncomputable def slowQuadraticSolver (state : ℝ) : ℝ :=
  (1 - slowRate) * state

noncomputable def quadraticEnergy (state : ℝ) : ℝ :=
  state ^ 2 / 2

noncomputable def slowQuadraticContraction :
    ContractionCertificate slowQuadraticSolver where
  factor := 1 - slowRate
  factor_nonneg := by norm_num [slowRate]
  factor_lt_one := by norm_num [slowRate]
  contracts := by
    intro left right
    rw [show slowQuadraticSolver left - slowQuadraticSolver right =
        (1 - slowRate) * (left - right) by
      simp [slowQuadraticSolver]
      ring]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    norm_num [slowRate]

theorem slowQuadratic_zero_fixed :
    IsFixedPoint slowQuadraticSolver 0 := by
  norm_num [IsFixedPoint, slowQuadraticSolver]

theorem slowQuadratic_decrement_at_one :
    quadraticEnergy 1 - quadraticEnergy (slowQuadraticSolver 1) =
      slowRate - slowRate ^ 2 / 2 := by
  norm_num [quadraticEnergy, slowQuadraticSolver]
  ring

/-- The raw decrement is below `10^-3` although the state is still unit
distance from the unique fixed point. -/
theorem raw_energy_decrement_can_stop_far :
    quadraticEnergy 1 - quadraticEnergy (slowQuadraticSolver 1) <
        (1 / 1000 : ℝ) ∧
      ‖(1 : ℝ) - 0‖ = 1 := by
  constructor
  · rw [slowQuadratic_decrement_at_one]
    norm_num [slowRate]
  · norm_num

/-- The contraction-normalized residual criterion does not accept that same
state at distance tolerance `1/10`. -/
theorem normalized_residual_rejects_slow_far :
    ¬ ‖(1 : ℝ) - slowQuadraticSolver 1‖ <
        (1 - slowQuadraticContraction.factor) * (1 / 10 : ℝ) := by
  norm_num [slowQuadraticSolver, slowQuadraticContraction, slowRate]

#print axioms residual_sq_le_tolerance_div
#print axioms fixedPoint_scaled_sq_le_tolerance
#print axioms slowQuadratic_zero_fixed
#print axioms raw_energy_decrement_can_stop_far
#print axioms normalized_residual_rejects_slow_far

end EnergyDecrementStopping

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
