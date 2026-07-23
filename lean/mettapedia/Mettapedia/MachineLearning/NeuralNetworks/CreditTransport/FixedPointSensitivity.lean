import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ParameterTracking

/-!
# Fixed-point sensitivity for changing credit solvers

Finite tracking needs a bound on how far the solved state moves when data,
parameters, or continuation controls change.  This file derives that bound
from the change in the solver map.  Global contractions need no neighborhood
premise.  Local contractions require the previous fixed point to remain in
the next solver's certified ball; an explicit counterexample shows that this
overlap condition cannot be removed.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FixedPointSensitivity

open AmortizedInitialization
open LocalAmortizedInitialization
open ParameterTracking

variable {Parameter State : Type*} [NormedAddCommGroup State]

/-- For globally contractive solvers, displacement of the fixed point is
bounded by solver displacement at the previous fixed point, amplified by the
inverse contraction margin. -/
theorem global_target_drift_le_solver_change_div
    {solver : Parameter → State → State} {target : Parameter → State}
    (certificate : ∀ parameter, ContractionCertificate (solver parameter))
    (target_fixed : ∀ parameter,
      IsFixedPoint (solver parameter) (target parameter))
    (previous next : Parameter) :
    ‖target previous - target next‖ ≤
      ‖solver previous (target previous) -
          solver next (target previous)‖ /
        (1 - (certificate next).factor) := by
  have hresidual := fixedPoint_distance_le_residual_div
    (certificate next) (target next) (target previous) (target_fixed next)
  calc
    ‖target previous - target next‖ ≤
        ‖target previous - solver next (target previous)‖ /
          (1 - (certificate next).factor) := hresidual
    _ = ‖solver previous (target previous) -
          solver next (target previous)‖ /
        (1 - (certificate next).factor) := by
      rw [target_fixed previous]

/-- The local counterpart of `global_target_drift_le_solver_change_div`.
The old fixed point must lie in the next certified neighborhood because the
next contraction estimate is unavailable outside it. -/
theorem local_target_drift_le_solver_change_div
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (previous next : Parameter)
    (hpreviousMem :
      InClosedBall (target next) radius (target previous)) :
    ‖target previous - target next‖ ≤
      ‖solver previous (target previous) -
          solver next (target previous)‖ /
        (1 - (family.certificate next).factor) := by
  have htargetMem :
      InClosedBall (target next) radius (target next) := by
    simp [InClosedBall, (family.certificate next).radius_nonneg]
  have hresidual :=
    LocalAmortizedInitialization.fixedPoint_distance_le_residual_div
      (family.certificate next) (target next) (target previous)
      htargetMem hpreviousMem (family.target_fixed next)
  calc
    ‖target previous - target next‖ ≤
        ‖target previous - solver next (target previous)‖ /
          (1 - (family.certificate next).factor) := hresidual
    _ = ‖solver previous (target previous) -
          solver next (target previous)‖ /
        (1 - (family.certificate next).factor) := by
      rw [family.target_fixed previous]

/-- A Lipschitz bound on the solver map at the previous fixed point yields a
global parameter-to-fixed-point sensitivity bound. -/
theorem global_target_drift_le_parameter_distance_div
    [PseudoMetricSpace Parameter]
    {solver : Parameter → State → State} {target : Parameter → State}
    (certificate : ∀ parameter, ContractionCertificate (solver parameter))
    (target_fixed : ∀ parameter,
      IsFixedPoint (solver parameter) (target parameter))
    (previous next : Parameter) (solverSensitivity : ℝ)
    (hsolverChange :
      ‖solver previous (target previous) -
          solver next (target previous)‖ ≤
        solverSensitivity * dist previous next) :
    ‖target previous - target next‖ ≤
      (solverSensitivity * dist previous next) /
        (1 - (certificate next).factor) := by
  have hdenominator : 0 ≤ 1 - (certificate next).factor := by
    linarith [(certificate next).factor_lt_one]
  exact le_trans
    (global_target_drift_le_solver_change_div certificate target_fixed
      previous next)
    (div_le_div_of_nonneg_right hsolverChange hdenominator)

/-- A local parameter-to-fixed-point sensitivity bound.  The cross-target
membership premise is the branch-overlap obligation for a continuation step. -/
theorem local_target_drift_le_parameter_distance_div
    [PseudoMetricSpace Parameter]
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (previous next : Parameter) (solverSensitivity : ℝ)
    (hpreviousMem :
      InClosedBall (target next) radius (target previous))
    (hsolverChange :
      ‖solver previous (target previous) -
          solver next (target previous)‖ ≤
        solverSensitivity * dist previous next) :
    ‖target previous - target next‖ ≤
      (solverSensitivity * dist previous next) /
        (1 - (family.certificate next).factor) := by
  have hdenominator : 0 ≤ 1 - (family.certificate next).factor := by
    linarith [(family.certificate next).factor_lt_one]
  exact le_trans
    (local_target_drift_le_solver_change_div family previous next hpreviousMem)
    (div_le_div_of_nonneg_right hsolverChange hdenominator)

/-- Solver sensitivity discharges the target-drift premise of finite local
tracking.  The initializer error and the contraction-amplified solver change
must jointly fit inside the next certified ball. -/
theorem parameterized_iterate_tracking_of_solver_change_le
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (previous next : Parameter) (state : State) (error solverChange : ℝ)
    (herror : ‖state - target previous‖ ≤ error)
    (hpreviousMem :
      InClosedBall (target next) radius (target previous))
    (hsolverChange :
      ‖solver previous (target previous) -
          solver next (target previous)‖ ≤ solverChange)
    (hadmission :
      error + solverChange / (1 - (family.certificate next).factor) ≤
        radius)
    (steps : ℕ) :
    ‖(solver next)^[steps] state - target next‖ ≤
      (family.certificate next).factor ^ steps *
        (error + solverChange /
          (1 - (family.certificate next).factor)) := by
  have hdenominator : 0 ≤ 1 - (family.certificate next).factor := by
    linarith [(family.certificate next).factor_lt_one]
  have hdrift :
      ‖target previous - target next‖ ≤
        solverChange / (1 - (family.certificate next).factor) :=
    le_trans
      (local_target_drift_le_solver_change_div family previous next
        hpreviousMem)
      (div_le_div_of_nonneg_right hsolverChange hdenominator)
  exact parameterized_iterate_tracking_le family previous next state
    error (solverChange / (1 - (family.certificate next).factor))
    herror hdrift hadmission steps

/-- The fully parameterized tracking bound.  A Lipschitz estimate for the
solver family is amplified by the inverse contraction margin and then added
to inherited initialization error before finite settling. -/
theorem parameterized_iterate_tracking_of_parameter_distance_le
    [PseudoMetricSpace Parameter]
    {solver : Parameter → State → State} {target : Parameter → State}
    {radius : ℝ}
    (family : LocalSolverFamily solver target radius)
    (previous next : Parameter) (state : State)
    (error solverSensitivity : ℝ)
    (herror : ‖state - target previous‖ ≤ error)
    (hpreviousMem :
      InClosedBall (target next) radius (target previous))
    (hsolverChange :
      ‖solver previous (target previous) -
          solver next (target previous)‖ ≤
        solverSensitivity * dist previous next)
    (hadmission :
      error +
          (solverSensitivity * dist previous next) /
            (1 - (family.certificate next).factor) ≤ radius)
    (steps : ℕ) :
    ‖(solver next)^[steps] state - target next‖ ≤
      (family.certificate next).factor ^ steps *
        (error +
          (solverSensitivity * dist previous next) /
            (1 - (family.certificate next).factor)) := by
  exact parameterized_iterate_tracking_of_solver_change_le family
    previous next state error (solverSensitivity * dist previous next)
    herror hpreviousMem hsolverChange hadmission steps

/-! ## Exact positive fixture -/

/-- The half-step family is globally contractive for every target. -/
noncomputable def shiftedHalfGlobalCertificate (target : ℝ) :
    ContractionCertificate (shiftedHalfSolver target) where
  factor := 1 / 2
  factor_nonneg := by norm_num
  factor_lt_one := by norm_num
  contracts := by
    intro left right
    have hrewrite :
        shiftedHalfSolver target left - shiftedHalfSolver target right =
          (left - right) / 2 := by
      simp [shiftedHalfSolver]
      ring
    rw [hrewrite, Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    norm_num [div_eq_mul_inv, mul_comm]

theorem shiftedHalf_global_target_fixed (target : ℝ) :
    IsFixedPoint (shiftedHalfSolver target) target := by
  simp [IsFixedPoint, shiftedHalfSolver]

/-- For the half-step solver, the sensitivity certificate is exact: solver
change is half the target change, and the inverse contraction margin restores
the full displacement. -/
theorem shiftedHalf_sensitivity_bound_exact :
    ‖(0 : ℝ) - 1 / 4‖ =
      ‖shiftedHalfSolver 0 0 - shiftedHalfSolver (1 / 4) 0‖ /
        (1 - (shiftedHalfGlobalCertificate (1 / 4)).factor) := by
  norm_num [shiftedHalfSolver, shiftedHalfGlobalCertificate, Real.norm_eq_abs]

theorem shiftedHalf_parameter_sensitivity_bound_exact :
    ‖(0 : ℝ) - 1 / 4‖ =
      ((1 / 2 : ℝ) * dist (0 : ℝ) (1 / 4 : ℝ)) /
        (1 - (shiftedHalfGlobalCertificate (1 / 4)).factor) := by
  norm_num [shiftedHalfGlobalCertificate, Real.dist_eq, Real.norm_eq_abs]

theorem shiftedHalf_global_target_drift_le :
    ‖(0 : ℝ) - 1 / 4‖ ≤
      ‖shiftedHalfSolver 0 0 - shiftedHalfSolver (1 / 4) 0‖ /
        (1 - (shiftedHalfGlobalCertificate (1 / 4)).factor) := by
  exact global_target_drift_le_solver_change_div shiftedHalfGlobalCertificate
    shiftedHalf_global_target_fixed 0 (1 / 4)

theorem shiftedHalf_twoStep_tracking_from_solver_change :
    ‖(shiftedHalfSolver (1 / 4))^[2] (1 / 2) - 1 / 4‖ ≤
      (shiftedHalfFamily.certificate (1 / 4)).factor ^ 2 *
        ((1 / 2 : ℝ) +
          (1 / 8 : ℝ) /
            (1 - (shiftedHalfFamily.certificate (1 / 4)).factor)) := by
  apply parameterized_iterate_tracking_of_solver_change_le shiftedHalfFamily
    (0 : ℝ) (1 / 4 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 8 : ℝ)
  · norm_num [Real.norm_eq_abs]
  · norm_num [InClosedBall, Real.norm_eq_abs]
  · norm_num [shiftedHalfSolver, Real.norm_eq_abs]
  · norm_num [shiftedHalfFamily]

/-- Raw solver displacement alone is not a fixed-point-drift bound.  The
inverse contraction margin is necessary even in this affine family. -/
theorem shiftedHalf_raw_solver_change_underestimates_target_drift :
    ‖shiftedHalfSolver 0 0 - shiftedHalfSolver 1 0‖ <
      ‖(0 : ℝ) - 1‖ := by
  norm_num [shiftedHalfSolver, Real.norm_eq_abs]

/-! ## Local branch-overlap boundary -/

def separatedTarget : Bool → ℝ
  | false => 0
  | true => 3

noncomputable def separatedLocalSolver : Bool → ℝ → ℝ
  | false, _ => 0
  | true, state => if state = 0 then 0 else 3

noncomputable def separatedLocalFamily :
    LocalSolverFamily separatedLocalSolver separatedTarget 1 where
  certificate := by
    intro parameter
    refine
      { factor := 0
        factor_nonneg := by norm_num
        factor_lt_one := by norm_num
        radius_nonneg := by norm_num
        maps_ball := ?_
        contracts_on_ball := ?_ }
    · cases parameter with
      | false =>
          intro state _
          norm_num [separatedLocalSolver, separatedTarget, InClosedBall]
      | true =>
          intro state hstate
          have hstateNe : state ≠ 0 := by
            intro hzero
            subst state
            norm_num [separatedTarget, InClosedBall, Real.norm_eq_abs] at hstate
          simp [separatedLocalSolver, separatedTarget, hstateNe, InClosedBall]
    · cases parameter with
      | false =>
          intro left right _ _
          simp [separatedLocalSolver]
      | true =>
          intro left right hleft hright
          have hleftNe : left ≠ 0 := by
            intro hzero
            subst left
            norm_num [separatedTarget, InClosedBall, Real.norm_eq_abs] at hleft
          have hrightNe : right ≠ 0 := by
            intro hzero
            subst right
            norm_num [separatedTarget, InClosedBall, Real.norm_eq_abs] at hright
          simp [separatedLocalSolver, hleftNe, hrightNe]
  target_fixed := by
    intro parameter
    cases parameter <;>
      norm_num [IsFixedPoint, separatedLocalSolver, separatedTarget]

/-- Without overlap of the two local branches, solver displacement at the
old fixed point can be zero while the fixed points are three units apart. -/
theorem separatedLocalFamily_no_sensitivity_without_overlap :
    ‖separatedLocalSolver false (separatedTarget false) -
        separatedLocalSolver true (separatedTarget false)‖ = 0 ∧
      ‖separatedTarget false - separatedTarget true‖ = 3 := by
  norm_num [separatedLocalSolver, separatedTarget, Real.norm_eq_abs]

theorem separatedLocalFamily_oldTarget_outside_nextBall :
    ¬ InClosedBall (separatedTarget true) 1 (separatedTarget false) := by
  norm_num [separatedTarget, InClosedBall, Real.norm_eq_abs]

#print axioms global_target_drift_le_solver_change_div
#print axioms local_target_drift_le_solver_change_div
#print axioms global_target_drift_le_parameter_distance_div
#print axioms local_target_drift_le_parameter_distance_div
#print axioms parameterized_iterate_tracking_of_solver_change_le
#print axioms parameterized_iterate_tracking_of_parameter_distance_le
#print axioms shiftedHalf_sensitivity_bound_exact
#print axioms shiftedHalf_parameter_sensitivity_bound_exact
#print axioms shiftedHalf_twoStep_tracking_from_solver_change
#print axioms shiftedHalf_raw_solver_change_underestimates_target_drift
#print axioms separatedLocalFamily_no_sensitivity_without_overlap

end FixedPointSensitivity

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
