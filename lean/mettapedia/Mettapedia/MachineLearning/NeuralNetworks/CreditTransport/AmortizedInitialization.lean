import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PrimalDualContinuation

/-!
# Amortized initialization and tracking for contractive credit solvers

An amortized initializer may choose the starting primal/dual state, while a
subsequent characterized solver owns the fixed point.  The theorems below
make that distinction exact: contraction gives a unique fixed point, geometric
initializer-error decay, an adaptive residual certificate, and a moving-target
tracking budget.  A direct head with no corrective solve is outside this warm-
start guarantee.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace AmortizedInitialization

variable {State : Type*} [NormedAddCommGroup State]

/-- A global contraction certificate for a declared solver map. -/
structure ContractionCertificate (solver : State → State) where
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  factor_lt_one : factor < 1
  contracts : ∀ left right,
    ‖solver left - solver right‖ ≤ factor * ‖left - right‖

def IsFixedPoint (solver : State → State) (state : State) : Prop :=
  solver state = state

/-- A contractive solver has at most one fixed point.  This is the fixed-point
part of initializer invariance: no initializer can select a different solved
state while the characterized solver is run to its fixed point. -/
theorem fixedPoint_unique
    {solver : State → State} (certificate : ContractionCertificate solver)
    {left right : State}
    (hleft : IsFixedPoint solver left) (hright : IsFixedPoint solver right) :
    left = right := by
  have hcontract := certificate.contracts left right
  rw [hleft, hright] at hcontract
  have hzero : ‖left - right‖ = 0 := by
    by_contra hne
    have hpositive : 0 < ‖left - right‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hstrict :
        certificate.factor * ‖left - right‖ < ‖left - right‖ := by
      simpa using mul_lt_mul_of_pos_right certificate.factor_lt_one hpositive
    exact (not_lt_of_ge hcontract) hstrict
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Geometric dependence on the initializer after a finite number of solver
steps. -/
theorem iterate_initializer_distance_le
    {solver : State → State} (certificate : ContractionCertificate solver)
    (left right : State) (steps : ℕ) :
    ‖solver^[steps] left - solver^[steps] right‖ ≤
      certificate.factor ^ steps * ‖left - right‖ := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
      calc
        ‖solver (solver^[steps] left) - solver (solver^[steps] right)‖ ≤
            certificate.factor *
              ‖solver^[steps] left - solver^[steps] right‖ :=
          certificate.contracts _ _
        _ ≤ certificate.factor *
              (certificate.factor ^ steps * ‖left - right‖) := by
          exact mul_le_mul_of_nonneg_left inductionHypothesis
            certificate.factor_nonneg
        _ = certificate.factor ^ steps.succ * ‖left - right‖ := by
          rw [pow_succ']
          ac_rfl

/-- Distance from any amortized initializer to the invariant fixed point. -/
theorem iterate_initializer_to_fixedPoint_le
    {solver : State → State} (certificate : ContractionCertificate solver)
    (target initial : State) (htarget : IsFixedPoint solver target)
    (steps : ℕ) :
    ‖solver^[steps] initial - target‖ ≤
      certificate.factor ^ steps * ‖initial - target‖ := by
  have htargetIterate : solver^[steps] target = target := by
    induction steps with
    | zero => simp
    | succ steps inductionHypothesis =>
        rw [Function.iterate_succ_apply', inductionHypothesis, htarget]
  simpa [htargetIterate] using
    iterate_initializer_distance_le certificate initial target steps

/-- A closer initializer yields a no-worse certified finite-iteration bound. -/
theorem better_initializer_reduces_geometric_bound
    {solver : State → State} (certificate : ContractionCertificate solver)
    (target warm cold : State) (steps : ℕ)
    (hbetter : ‖warm - target‖ ≤ ‖cold - target‖) :
    certificate.factor ^ steps * ‖warm - target‖ ≤
      certificate.factor ^ steps * ‖cold - target‖ := by
  exact mul_le_mul_of_nonneg_left hbetter
    (pow_nonneg certificate.factor_nonneg steps)

/-- Solver residual controls fixed-point error.  This is the reusable basis
for an adaptive stopping rule that does not inspect the unknown true error. -/
theorem fixedPoint_distance_le_residual_div
    {solver : State → State} (certificate : ContractionCertificate solver)
    (target state : State) (htarget : IsFixedPoint solver target) :
    ‖state - target‖ ≤
      ‖state - solver state‖ / (1 - certificate.factor) := by
  have honeMinus : 0 < 1 - certificate.factor := by
    linarith [certificate.factor_lt_one]
  have htriangle :
      ‖state - target‖ ≤
        ‖state - solver state‖ + ‖solver state - target‖ := by
    have hraw := norm_add_le
      (state - solver state) (solver state - solver target)
    rw [htarget] at hraw
    simpa [sub_eq_add_neg, add_assoc] using hraw
  have hcontract := certificate.contracts state target
  rw [htarget] at hcontract
  apply (le_div_iff₀ honeMinus).2
  nlinarith

/-- If the observable solver residual is below `(1-q) * tolerance`, then the
actual fixed-point error is below the requested tolerance. -/
theorem residual_adaptiveStop
    {solver : State → State} (certificate : ContractionCertificate solver)
    (target state : State) (htarget : IsFixedPoint solver target)
    (tolerance : ℝ) (hresidual :
      ‖state - solver state‖ < (1 - certificate.factor) * tolerance) :
    ‖state - target‖ < tolerance := by
  have honeMinus : 0 < 1 - certificate.factor := by
    linarith [certificate.factor_lt_one]
  have hbound := fixedPoint_distance_le_residual_div
    certificate target state htarget
  have hresidualDiv :
      ‖state - solver state‖ / (1 - certificate.factor) < tolerance :=
    (div_lt_iff₀ honeMinus).2 (by simpa [mul_comm] using hresidual)
  exact lt_of_le_of_lt hbound hresidualDiv

/-- One solver step followed by a moving target incurs contraction error plus
the target drift. -/
theorem oneStep_tracking_le
    {solver : State → State} (certificate : ContractionCertificate solver)
    (currentTarget nextTarget state : State)
    (hcurrent : IsFixedPoint solver currentTarget) :
    ‖solver state - nextTarget‖ ≤
      certificate.factor * ‖state - currentTarget‖ +
        ‖currentTarget - nextTarget‖ := by
  calc
    ‖solver state - nextTarget‖ ≤
        ‖solver state - solver currentTarget‖ +
          ‖solver currentTarget - nextTarget‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        norm_add_le (solver state - solver currentTarget)
          (solver currentTarget - nextTarget)
    _ ≤ certificate.factor * ‖state - currentTarget‖ +
          ‖solver currentTarget - nextTarget‖ := by
      gcongr
      exact certificate.contracts _ _
    _ = certificate.factor * ‖state - currentTarget‖ +
          ‖currentTarget - nextTarget‖ := by rw [hcurrent]

/-- Explicit error-and-drift budget for a moving continuation target. -/
theorem oneStep_tracking_budget
    {solver : State → State} (certificate : ContractionCertificate solver)
    (currentTarget nextTarget state : State) (error drift : ℝ)
    (hcurrent : IsFixedPoint solver currentTarget)
    (herror : ‖state - currentTarget‖ ≤ error)
    (hdrift : ‖currentTarget - nextTarget‖ ≤ drift) :
    ‖solver state - nextTarget‖ ≤ certificate.factor * error + drift := by
  calc
    ‖solver state - nextTarget‖ ≤
        certificate.factor * ‖state - currentTarget‖ +
          ‖currentTarget - nextTarget‖ :=
      oneStep_tracking_le certificate currentTarget nextTarget state hcurrent
    _ ≤ certificate.factor * error + drift := by
      have hscaled := mul_le_mul_of_nonneg_left herror
        certificate.factor_nonneg
      linarith

/-- A drift budget preserving a declared invariant tracking radius. -/
theorem oneStep_preserves_trackingRadius
    {solver : State → State} (certificate : ContractionCertificate solver)
    (currentTarget nextTarget state : State) (radius drift : ℝ)
    (hcurrent : IsFixedPoint solver currentTarget)
    (hstate : ‖state - currentTarget‖ ≤ radius)
    (htargetDrift : ‖currentTarget - nextTarget‖ ≤ drift)
    (hbudget : certificate.factor * radius + drift ≤ radius) :
    ‖solver state - nextTarget‖ ≤ radius := by
  exact le_trans
    (oneStep_tracking_budget certificate currentTarget nextTarget state
      radius drift hcurrent hstate htargetDrift)
    hbudget

/-! ## Executable boundary fixtures -/

noncomputable def halfSolver (state : ℝ) : ℝ := state / 2

noncomputable def halfSolverCertificate : ContractionCertificate halfSolver where
  factor := 1 / 2
  factor_nonneg := by norm_num
  factor_lt_one := by norm_num
  contracts := by
    intro left right
    rw [show halfSolver left - halfSolver right = (left - right) / 2 by
      simp [halfSolver]; ring]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    norm_num
    have heq : |left - right| / 2 = (1 / 2 : ℝ) * |left - right| := by
      ring
    rw [heq]

theorem halfSolver_zero_fixed : IsFixedPoint halfSolver 0 := by
  norm_num [IsFixedPoint, halfSolver]

theorem halfSolver_warmStart_beats_stale_after_one :
    |halfSolver 1| < |halfSolver 4| := by
  norm_num [halfSolver]

/-- Even a contractive solver cannot remain in a unit tracking ball when the
target itself jumps by two before one corrective step. -/
theorem halfSolver_excessiveTargetDrift_leaves_unitBall :
    ¬ |halfSolver 0 - 2| ≤ 1 := by
  norm_num [halfSolver]

/-- A direct initializer readout and a corrected warm start are observably
different in general; the latter is not merely a synthetic-gradient head. -/
theorem halfSolver_directHead_ne_correctedWarmStart :
    (4 : ℝ) ≠ halfSolver 4 := by
  norm_num [halfSolver]

#print axioms fixedPoint_unique
#print axioms iterate_initializer_to_fixedPoint_le
#print axioms fixedPoint_distance_le_residual_div
#print axioms residual_adaptiveStop
#print axioms oneStep_tracking_budget
#print axioms halfSolver_excessiveTargetDrift_leaves_unitBall

end AmortizedInitialization

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
