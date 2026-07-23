import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ProspectiveResidualSemantics

/-!
# Error-coordinate residual semantics

Deep error-coordinate inference optimizes task loss through an error-state
readout plus a quadratic penalty centered at zero error.  On the active
masked product space, its energy gradient is the task gradient plus precision
times the error state.  This is the zero-input specialization of the same
unit-resolvent equation used by prospective latent settling.

The algebraic residual identity needs only nonzero precision.  Turning that
residual into distance from an exact equilibrium additionally needs the
quadratic precision to dominate any negative task curvature.  This strictly
extends the monotone-task case: a mildly concave scalar task is certified by
the corrected `precision - rho` denominator, while the boundary case has
multiple stationary states.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ErrorCoordinateResidualSemantics

open scoped InnerProductSpace
open NonlinearResolvent
open ResolverResidual
open ProspectiveResidualSemantics

noncomputable section

variable {ErrorState : Type*}
  [NormedAddCommGroup ErrorState] [InnerProductSpace ℝ ErrorState]

/-! ## Zero-centered error-coordinate equation -/

/-- Gradient of task loss through the error-state readout plus the quadratic
error-coordinate penalty on the active product space. -/
def errorCoordinateEnergyGradient
    (precision : ℝ) (taskGradient : ErrorState → ErrorState)
    (error : ErrorState) : ErrorState :=
  taskGradient error + precision • error

/-- Error-coordinate energy is the zero-prediction specialization of the
prospective energy-gradient equation. -/
theorem errorCoordinateEnergyGradient_eq_prospective
    (precision : ℝ) (taskGradient : ErrorState → ErrorState)
    (error : ErrorState) :
    errorCoordinateEnergyGradient precision taskGradient error =
      prospectiveEnergyGradient 0 precision taskGradient error := by
  simp [errorCoordinateEnergyGradient, prospectiveEnergyGradient]

/-- The deep error-coordinate equation residual at zero input is exactly the
final energy gradient scaled by inverse precision. -/
theorem resolverEquationResidual_eq_inv_smul_energyGradient
    (precision : ℝ) (taskGradient : ErrorState → ErrorState)
    (error : ErrorState) (hprecision : precision ≠ 0) :
    resolverEquationResidual
        (prospectiveImplicitOperator precision taskGradient) 0 error =
      precision⁻¹ •
        errorCoordinateEnergyGradient precision taskGradient error := by
  rw [errorCoordinateEnergyGradient_eq_prospective]
  exact
    ProspectiveResidualSemantics.resolverEquationResidual_eq_inv_smul_energyGradient
      0 precision taskGradient error hprecision

/-- Norm form of the exact error-coordinate residual identity. -/
theorem norm_resolverEquationResidual_eq_energyGradient_div
    (precision : ℝ) (taskGradient : ErrorState → ErrorState)
    (error : ErrorState) (hprecision : 0 < precision) :
    ‖resolverEquationResidual
        (prospectiveImplicitOperator precision taskGradient) 0 error‖ =
      ‖errorCoordinateEnergyGradient precision taskGradient error‖ /
        precision := by
  rw [errorCoordinateEnergyGradient_eq_prospective]
  exact
    ProspectiveResidualSemantics.norm_resolverEquationResidual_eq_energyGradient_div
      0 precision taskGradient error hprecision

/-! ## Curvature-dominated residual certificate -/

/-- A `rho`-hypomonotone task gradient becomes strongly monotone after adding
quadratic precision, with the exact remaining modulus `precision - rho`. -/
theorem errorCoordinateEnergyGradient_stronglyMonotone
    (precision rho : ℝ) (taskGradient : ErrorState → ErrorState)
    (htask : HypomonotoneMap rho taskGradient) :
    StronglyMonotoneMap (precision - rho)
      (errorCoordinateEnergyGradient precision taskGradient) := by
  exact stronglyMonotone_add_smul_id htask

/-- The exact zero-input resolver output is stationary for the full
error-coordinate energy.  This algebraic fact needs nonzero precision but no
convexity or monotonicity assumption. -/
theorem exactResolver_zero_is_stationary
    {exactResolver : ErrorState → ErrorState}
    (precision : ℝ) (taskGradient : ErrorState → ErrorState)
    (hprecision : precision ≠ 0)
    (resolventEquation : IsUnitResolventMapOf
      (prospectiveImplicitOperator precision taskGradient) exactResolver) :
    errorCoordinateEnergyGradient precision taskGradient
        (exactResolver 0) = 0 := by
  have hresidual :
      resolverEquationResidual
          (prospectiveImplicitOperator precision taskGradient)
          0 (exactResolver 0) = 0 := by
    simp only [resolverEquationResidual]
    rw [resolventEquation 0]
    exact sub_self 0
  rw [resolverEquationResidual_eq_inv_smul_energyGradient
    precision taskGradient (exactResolver 0) hprecision] at hresidual
  exact (smul_eq_zero.mp hresidual).resolve_left (inv_ne_zero hprecision)

/-- If precision strictly dominates the declared negative-curvature budget,
the observable final energy gradient bounds distance to the exact error-state
equilibrium with denominator `precision - rho`. -/
theorem distance_exactErrorState_le_finalGradient_div_curvatureGap
    {exactResolver : ErrorState → ErrorState}
    (precision rho : ℝ) (taskGradient : ErrorState → ErrorState)
    (error : ErrorState) (hprecision : precision ≠ 0)
    (hdominates : rho < precision)
    (htask : HypomonotoneMap rho taskGradient)
    (resolventEquation : IsUnitResolventMapOf
      (prospectiveImplicitOperator precision taskGradient) exactResolver) :
    ‖error - exactResolver 0‖ ≤
      ‖errorCoordinateEnergyGradient precision taskGradient error‖ /
        (precision - rho) := by
  exact (errorCoordinateEnergyGradient_stronglyMonotone
    precision rho taskGradient htask).distance_root_le_norm_div
      (sub_pos.mpr hdominates)
      (exactResolver_zero_is_stationary precision taskGradient
        hprecision resolventEquation)

/-- Under the same strict curvature gap, the stationary error-coordinate
state is unique. -/
theorem stationary_unique_of_precision_dominates
    (precision rho : ℝ) (taskGradient : ErrorState → ErrorState)
    (hdominates : rho < precision)
    (htask : HypomonotoneMap rho taskGradient)
    {left right : ErrorState}
    (hleft : errorCoordinateEnergyGradient precision taskGradient left = 0)
    (hright : errorCoordinateEnergyGradient precision taskGradient right = 0) :
    left = right := by
  exact (errorCoordinateEnergyGradient_stronglyMonotone
    precision rho taskGradient htask).root_unique
      (sub_pos.mpr hdominates) hleft hright

/-- Under task-gradient monotonicity, the observable final gradient also
bounds distance from the exact zero-input error-coordinate equilibrium. -/
theorem distance_exactErrorState_le_finalGradient_div
    {exactResolver : ErrorState → ErrorState}
    (precision : ℝ) (taskGradient : ErrorState → ErrorState)
    (error : ErrorState) (hprecision : 0 < precision)
    (htask : MonotoneMap taskGradient)
    (resolventEquation : IsUnitResolventMapOf
      (prospectiveImplicitOperator precision taskGradient) exactResolver) :
    ‖error - exactResolver 0‖ ≤
      ‖errorCoordinateEnergyGradient precision taskGradient error‖ /
        precision := by
  rw [errorCoordinateEnergyGradient_eq_prospective]
  exact
    ProspectiveResidualSemantics.distance_exactProspectiveState_le_finalGradient_div
      0 precision taskGradient error hprecision htask resolventEquation

/-- Under the same monotonicity premise, exact stationarity identifies the
exact error-coordinate equilibrium. -/
theorem stationary_iff_exactErrorState
    {exactResolver : ErrorState → ErrorState}
    (precision : ℝ) (taskGradient : ErrorState → ErrorState)
    (error : ErrorState) (hprecision : 0 < precision)
    (htask : MonotoneMap taskGradient)
    (resolventEquation : IsUnitResolventMapOf
      (prospectiveImplicitOperator precision taskGradient) exactResolver) :
    errorCoordinateEnergyGradient precision taskGradient error = 0 ↔
      error = exactResolver 0 := by
  rw [errorCoordinateEnergyGradient_eq_prospective]
  exact ProspectiveResidualSemantics.stationary_iff_exactProspectiveState
    0 precision taskGradient error hprecision htask resolventEquation

/-! ## Nonzero positive fixture -/

def shiftedTaskGradient (error : ℝ) : ℝ := error - 2

def shiftedHalfResolver (input : ℝ) : ℝ := input / 2 + 1

theorem shiftedTaskGradient_monotone :
    MonotoneMap shiftedTaskGradient := by
  intro left right
  simp [shiftedTaskGradient]
  positivity

theorem shiftedTaskGradient_resolventEquation :
    IsUnitResolventMapOf
      (prospectiveImplicitOperator 1 shiftedTaskGradient)
      shiftedHalfResolver := by
  intro input
  simp [prospectiveImplicitOperator, shiftedTaskGradient,
    shiftedHalfResolver]
  ring

theorem shiftedErrorCoordinate_nonzero_equilibrium :
    errorCoordinateEnergyGradient 1 shiftedTaskGradient 1 = 0 ∧
      shiftedHalfResolver 0 = 1 := by
  norm_num [errorCoordinateEnergyGradient, shiftedTaskGradient,
    shiftedHalfResolver]

theorem shiftedErrorCoordinate_distance_certificate_at_two :
    ‖(2 : ℝ) - shiftedHalfResolver 0‖ ≤
      ‖errorCoordinateEnergyGradient 1 shiftedTaskGradient 2‖ / 1 := by
  exact distance_exactErrorState_le_finalGradient_div
    1 shiftedTaskGradient 2 (by norm_num) shiftedTaskGradient_monotone
      shiftedTaskGradient_resolventEquation

/-! ## Negative curvature: corrected denominator and sharp boundary -/

def weaklyConcaveTaskGradient (error : ℝ) : ℝ := -(9 / 10) * error

def weaklyConcaveResolver (input : ℝ) : ℝ := 10 * input

theorem weaklyConcaveTaskGradient_not_monotone :
    ¬ MonotoneMap weaklyConcaveTaskGradient := by
  intro claimed
  have contradicted := claimed (1 : ℝ) 0
  norm_num [weaklyConcaveTaskGradient] at contradicted

theorem weaklyConcaveTaskGradient_hypomonotone :
    HypomonotoneMap (9 / 10) weaklyConcaveTaskGradient := by
  intro left right
  norm_num [weaklyConcaveTaskGradient, Real.norm_eq_abs, sq_abs]
  ring_nf
  exact le_rfl

theorem weaklyConcave_resolventEquation :
    IsUnitResolventMapOf
      (prospectiveImplicitOperator 1 weaklyConcaveTaskGradient)
      weaklyConcaveResolver := by
  intro input
  simp [prospectiveImplicitOperator, weaklyConcaveTaskGradient,
    weaklyConcaveResolver]
  ring

/-- Without monotonicity, the algebraic residual remains exact but can be
strictly smaller than distance to the selected zero-input equilibrium. -/
theorem nonmonotone_residual_does_not_bound_equilibrium_distance :
    ‖resolverEquationResidual
        (prospectiveImplicitOperator 1 weaklyConcaveTaskGradient)
        0 1‖ <
      ‖(1 : ℝ) - weaklyConcaveResolver 0‖ := by
  norm_num [resolverEquationResidual, prospectiveImplicitOperator,
    weaklyConcaveTaskGradient, weaklyConcaveResolver, Real.norm_eq_abs]

/-- The curvature-corrected denominator exactly repairs the preceding failed
naive bound even though the task gradient itself is not monotone. -/
theorem weaklyConcave_curvatureGap_distance_certificate :
    ‖(1 : ℝ) - weaklyConcaveResolver 0‖ ≤
      ‖errorCoordinateEnergyGradient 1 weaklyConcaveTaskGradient 1‖ /
        (1 - 9 / 10) := by
  exact distance_exactErrorState_le_finalGradient_div_curvatureGap
    1 (9 / 10) weaklyConcaveTaskGradient 1 (by norm_num) (by norm_num)
      weaklyConcaveTaskGradient_hypomonotone
      weaklyConcave_resolventEquation

/-- At the sharp boundary `precision = rho`, quadratic precision can exactly
cancel task curvature, leaving distinct stationary states. -/
def criticalConcaveTaskGradient (error : ℝ) : ℝ := -error

theorem criticalConcaveTaskGradient_hypomonotone :
    HypomonotoneMap 1 criticalConcaveTaskGradient := by
  intro left right
  norm_num [criticalConcaveTaskGradient, Real.norm_eq_abs, sq_abs]
  ring_nf
  exact le_rfl

theorem equal_precision_curvature_has_nonunique_stationary_states :
    errorCoordinateEnergyGradient 1 criticalConcaveTaskGradient 0 = 0 ∧
      errorCoordinateEnergyGradient 1 criticalConcaveTaskGradient 1 = 0 ∧
      (0 : ℝ) ≠ 1 := by
  norm_num [errorCoordinateEnergyGradient, criticalConcaveTaskGradient]

#print axioms errorCoordinateEnergyGradient_eq_prospective
#print axioms resolverEquationResidual_eq_inv_smul_energyGradient
#print axioms norm_resolverEquationResidual_eq_energyGradient_div
#print axioms errorCoordinateEnergyGradient_stronglyMonotone
#print axioms exactResolver_zero_is_stationary
#print axioms distance_exactErrorState_le_finalGradient_div_curvatureGap
#print axioms stationary_unique_of_precision_dominates
#print axioms distance_exactErrorState_le_finalGradient_div
#print axioms stationary_iff_exactErrorState
#print axioms shiftedTaskGradient_resolventEquation
#print axioms shiftedErrorCoordinate_nonzero_equilibrium
#print axioms shiftedErrorCoordinate_distance_certificate_at_two
#print axioms weaklyConcaveTaskGradient_not_monotone
#print axioms weaklyConcave_resolventEquation
#print axioms nonmonotone_residual_does_not_bound_equilibrium_distance
#print axioms weaklyConcave_curvatureGap_distance_certificate
#print axioms equal_precision_curvature_has_nonunique_stationary_states

end

end ErrorCoordinateResidualSemantics

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
