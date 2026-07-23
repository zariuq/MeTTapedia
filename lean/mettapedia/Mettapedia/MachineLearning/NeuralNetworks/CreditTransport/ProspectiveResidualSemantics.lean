import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ResolverResidual

/-!
# Prospective residual settling as an implicit-solve certificate

Prospective residual inference freezes slow parameters and descends an energy
consisting of task loss plus a quadratic penalty around a predicted latent.
On the active masked latent subspace, stationarity of that energy is precisely
the unit-resolvent equation for the task gradient scaled by inverse penalty
precision.

This file proves the correspondence, the monotonicity condition needed to use
the residual certificate, and the resulting distance bound from a measurable
final energy gradient.  An exact scalar instance demonstrates the bridge.
A separate smooth counterexample shows that energy descent alone does not
bound the gradient at the accepted endpoint; final-gradient telemetry cannot
be reconstructed from a monotone energy trace without additional regularity.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ProspectiveResidualSemantics

open scoped InnerProductSpace
open NonlinearResolvent
open ResolverResidual
open AmortizedInitialization

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-! ## Source-level stationary equation -/

/-- Implicit operator induced by a task gradient and a positive quadratic
penalty precision. -/
def prospectiveImplicitOperator
    (precision : ℝ) (taskGradient : State → State) (state : State) : State :=
  precision⁻¹ • taskGradient state

/-- Gradient of task loss plus the quadratic prediction penalty on the active
latent state. -/
def prospectiveEnergyGradient
    (prediction : State) (precision : ℝ)
    (taskGradient : State → State) (state : State) : State :=
  taskGradient state + precision • (state - prediction)

/-- The resolvent-equation residual is exactly the energy gradient scaled by
inverse precision. -/
theorem resolverEquationResidual_eq_inv_smul_energyGradient
    (prediction : State) (precision : ℝ)
    (taskGradient : State → State) (state : State)
    (hprecision : precision ≠ 0) :
    resolverEquationResidual
        (prospectiveImplicitOperator precision taskGradient)
        prediction state =
      precision⁻¹ • prospectiveEnergyGradient
        prediction precision taskGradient state := by
  rw [prospectiveEnergyGradient, smul_add, smul_smul,
    inv_mul_cancel₀ hprecision, one_smul]
  simp only [resolverEquationResidual, prospectiveImplicitOperator]
  abel

/-- Positive inverse-precision scaling preserves monotonicity of the task
gradient. -/
theorem prospectiveImplicitOperator_monotone
    (precision : ℝ) (taskGradient : State → State)
    (hprecision : 0 < precision)
    (htask : MonotoneMap taskGradient) :
    MonotoneMap (prospectiveImplicitOperator precision taskGradient) := by
  intro left right
  have hbase :
      0 ≤ ⟪left - right, taskGradient left - taskGradient right⟫_ℝ :=
    htask left right
  have hinverse : 0 ≤ precision⁻¹ := (inv_nonneg.mpr hprecision.le)
  simpa only [prospectiveImplicitOperator, ← smul_sub,
    real_inner_smul_right] using mul_nonneg hinverse hbase

/-- Norm form of the source correspondence. -/
theorem norm_resolverEquationResidual_eq_energyGradient_div
    (prediction : State) (precision : ℝ)
    (taskGradient : State → State) (state : State)
    (hprecision : 0 < precision) :
    ‖resolverEquationResidual
        (prospectiveImplicitOperator precision taskGradient)
        prediction state‖ =
      ‖prospectiveEnergyGradient prediction precision taskGradient state‖ /
        precision := by
  rw [resolverEquationResidual_eq_inv_smul_energyGradient
    prediction precision taskGradient state hprecision.ne']
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hprecision)]
  simp [div_eq_mul_inv, mul_comm]

/-- Under task-gradient monotonicity, a final energy-gradient norm gives an
observable distance certificate to the exact prospective equilibrium. -/
theorem distance_exactProspectiveState_le_finalGradient_div
    {exactResolver : State → State}
    (prediction : State) (precision : ℝ)
    (taskGradient : State → State) (state : State)
    (hprecision : 0 < precision)
    (htask : MonotoneMap taskGradient)
    (resolventEquation : IsUnitResolventMapOf
      (prospectiveImplicitOperator precision taskGradient) exactResolver) :
    ‖state - exactResolver prediction‖ ≤
      ‖prospectiveEnergyGradient prediction precision taskGradient state‖ /
        precision := by
  calc
    ‖state - exactResolver prediction‖ ≤
        ‖resolverEquationResidual
          (prospectiveImplicitOperator precision taskGradient)
          prediction state‖ :=
      distance_exactResolvent_le_equationResidual
        (prospectiveImplicitOperator_monotone
          precision taskGradient hprecision htask)
        resolventEquation prediction state
    _ = ‖prospectiveEnergyGradient prediction precision taskGradient state‖ /
          precision :=
      norm_resolverEquationResidual_eq_energyGradient_div
        prediction precision taskGradient state hprecision

/-- Exact stationarity recovers the exact prospective resolvent output. -/
theorem stationary_iff_exactProspectiveState
    {exactResolver : State → State}
    (prediction : State) (precision : ℝ)
    (taskGradient : State → State) (state : State)
    (hprecision : 0 < precision)
    (htask : MonotoneMap taskGradient)
    (resolventEquation : IsUnitResolventMapOf
      (prospectiveImplicitOperator precision taskGradient) exactResolver) :
    prospectiveEnergyGradient prediction precision taskGradient state = 0 ↔
      state = exactResolver prediction := by
  constructor
  · intro hstationary
    apply zero_equationResidual_forces_exactResolverOutput
      (prospectiveImplicitOperator_monotone
        precision taskGradient hprecision htask)
      resolventEquation prediction state
    rw [resolverEquationResidual_eq_inv_smul_energyGradient
      prediction precision taskGradient state hprecision.ne', hstationary,
      smul_zero]
  · intro hequal
    have hresidual :
        resolverEquationResidual
          (prospectiveImplicitOperator precision taskGradient)
          prediction state = 0 := by
      rw [hequal]
      exact sub_eq_zero.mpr (resolventEquation prediction)
    rw [resolverEquationResidual_eq_inv_smul_energyGradient
      prediction precision taskGradient state hprecision.ne'] at hresidual
    exact (smul_eq_zero.mp hresidual).resolve_left (inv_ne_zero hprecision.ne')

/-! ## Explicit gradient-settling steps -/

/-- One explicit inference step, matching the accepted candidate before any
backtracking-specific rate selection. -/
def prospectiveGradientStep
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) (state : State) : State :=
  state - rate • prospectiveEnergyGradient
    prediction precision taskGradient state

theorem prospectiveGradientStep_displacement
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) (state : State) :
    state - prospectiveGradientStep prediction precision rate taskGradient state =
      rate • prospectiveEnergyGradient
        prediction precision taskGradient state := by
  simp [prospectiveGradientStep]

/-- A nonzero accepted rate lets the pre-step energy gradient be reconstructed
from the accepted displacement.  This identifies the gradient at the source
state, not at the accepted endpoint. -/
theorem prospectiveGradientStep_recovers_sourceGradient
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) (state : State)
    (hrate : rate ≠ 0) :
    rate⁻¹ •
        (state - prospectiveGradientStep
          prediction precision rate taskGradient state) =
      prospectiveEnergyGradient prediction precision taskGradient state := by
  rw [prospectiveGradientStep_displacement, smul_smul,
    inv_mul_cancel₀ hrate, one_smul]

/-! ## Exact positive scalar instance -/

def identityTaskGradient (state : ℝ) : ℝ := state

theorem identityTaskGradient_monotone :
    MonotoneMap identityTaskGradient := by
  intro left right
  simp [identityTaskGradient]
  positivity

theorem identityProspective_resolventEquation :
    IsUnitResolventMapOf
      (prospectiveImplicitOperator 1 identityTaskGradient) halfSolver := by
  intro input
  simp [prospectiveImplicitOperator, identityTaskGradient, halfSolver]

theorem identityProspective_oneStep_reaches_exactState :
    prospectiveGradientStep 2 1 (1 / 2) identityTaskGradient 2 = (1 : ℝ) ∧
      prospectiveEnergyGradient 2 1 identityTaskGradient 1 = 0 ∧
      halfSolver 2 = 1 := by
  norm_num [prospectiveGradientStep, prospectiveEnergyGradient,
    identityTaskGradient, halfSolver]

theorem identityProspective_stationary_iff (state : ℝ) :
    prospectiveEnergyGradient 2 1 identityTaskGradient state = 0 ↔
      state = halfSolver 2 := by
  exact stationary_iff_exactProspectiveState 2 1 identityTaskGradient state
    (by norm_num) identityTaskGradient_monotone
    identityProspective_resolventEquation

/-! ## Energy descent is not final-stationarity telemetry -/

def cubicEnergy (state : ℝ) : ℝ := state ^ 3

def cubicEnergyGradient (state : ℝ) : ℝ := 3 * state ^ 2

/-- A smooth gradient step can lower energy while increasing the gradient norm
at its accepted endpoint.  Therefore a monotone energy trace does not supply
the final-gradient residual required by the prospective certificate. -/
theorem energyDescent_does_not_bound_finalGradient :
    prospectiveGradientStep 0 0 2 cubicEnergyGradient (1 / 2) = (-1 : ℝ) ∧
      cubicEnergy (-1) < cubicEnergy (1 / 2) ∧
      ‖cubicEnergyGradient (1 / 2)‖ < ‖cubicEnergyGradient (-1)‖ := by
  norm_num [prospectiveGradientStep, prospectiveEnergyGradient,
    cubicEnergyGradient, cubicEnergy, Real.norm_eq_abs]

#print axioms resolverEquationResidual_eq_inv_smul_energyGradient
#print axioms prospectiveImplicitOperator_monotone
#print axioms norm_resolverEquationResidual_eq_energyGradient_div
#print axioms distance_exactProspectiveState_le_finalGradient_div
#print axioms stationary_iff_exactProspectiveState
#print axioms prospectiveGradientStep_displacement
#print axioms prospectiveGradientStep_recovers_sourceGradient
#print axioms identityProspective_oneStep_reaches_exactState
#print axioms identityProspective_stationary_iff
#print axioms energyDescent_does_not_bound_finalGradient

end

end ProspectiveResidualSemantics

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
