import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedSettlingTrace
import Mathlib.Analysis.Convex.Strong

/-!
# Conditional acceleration of predictive settling

Acceleration is licensed only after a curvature or contraction certificate.
The first part makes the curvature premise compositional: a task with lower
curvature bound `-rho` plus a `precision`-strongly-convex penalty is
`precision - rho` strongly convex.  Positive precision alone is insufficient.

The second part gives an exact executable quadratic witness.  On the slow mode
of a spectrum in `[1, 9]`, the standard strongly-convex Nesterov parameters
have residual `(1 + n / 3) * (2 / 3)^n`, whereas plain settling has residual
`(8 / 9)^n`.  The momentum-zero specialization reduces to plain settling.
Persistent oracle error and negative curvature have separate failure fixtures.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ConditionalAcceleration

open Set

variable {State : Type*} [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- A lower task-curvature certificate stated as strong convexity with a
possibly negative modulus. -/
def HasNegativeCurvatureBound
    (region : Set State) (rho : ℝ) (task : State → ℝ) : Prop :=
  StrongConvexOn region (-rho) task

/-- Precision dominates the declared negative task curvature by subtraction,
not merely by being positive. -/
theorem strongConvexOn_add_precision
    {region : Set State} {task penalty : State → ℝ} {rho precision : ℝ}
    (taskBound : HasNegativeCurvatureBound region rho task)
    (penaltyBound : StrongConvexOn region precision penalty) :
    StrongConvexOn region (precision - rho) (task + penalty) := by
  change UniformConvexOn region
    (fun radius => (precision - rho) / 2 * radius ^ 2) (task + penalty)
  change UniformConvexOn region
    (fun radius => (-rho) / 2 * radius ^ 2) task at taskBound
  change UniformConvexOn region
    (fun radius => precision / 2 * radius ^ 2) penalty at penaltyBound
  have combined := taskBound.add penaltyBound
  convert combined using 1
  ext radius
  simp only [Pi.add_apply]
  ring

/-- If precision strictly dominates the curvature defect, the combined energy
is strictly convex on the declared region. -/
theorem strictConvexOn_add_precision
    {region : Set State} {task penalty : State → ℝ} {rho precision : ℝ}
    (taskBound : HasNegativeCurvatureBound region rho task)
    (penaltyBound : StrongConvexOn region precision penalty)
    (dominates : rho < precision) :
    StrictConvexOn ℝ region (task + penalty) :=
  (strongConvexOn_add_precision taskBound penaltyBound).strictConvexOn
    (sub_pos.mpr dominates)

/-- Scalar quadratic used to instantiate the curvature ledger exactly. -/
noncomputable def scalarQuadratic (curvature state : ℝ) : ℝ :=
  curvature / 2 * state ^ 2

theorem scalarQuadratic_strongConvexOn (curvature : ℝ) :
    StrongConvexOn (Set.univ : Set ℝ) curvature
      (scalarQuadratic curvature) := by
  rw [strongConvexOn_iff_convex]
  simpa [scalarQuadratic, Real.norm_eq_abs, sq_abs] using
    (convexOn_const (𝕜 := ℝ) (E := ℝ) (β := ℝ) 0
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)))

/-- Positive precision does not rescue a task whose negative curvature is
larger: the resulting scalar energy fails even ordinary convexity. -/
theorem positivePrecision_alone_not_sufficient :
    ¬ ConvexOn ℝ Set.univ (fun state : ℝ => -(state ^ 2) / 2) := by
  intro claimed
  have midpoint := claimed.2 (Set.mem_univ (-1 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num at midpoint

/-! ## Exact scalar accelerated and plain modes -/

/-- Two consecutive scalar errors carried by a momentum method. -/
@[ext] structure MomentumState where
  previous : ℝ
  current : ℝ

/-- Nesterov look-ahead step for one scalar quadratic eigenmode. -/
noncomputable def momentumQuadraticStep
    (rate curvature momentum : ℝ) (state : MomentumState) : MomentumState :=
  { previous := state.current
    current :=
      (1 - rate * curvature) *
        (state.current + momentum * (state.current - state.previous)) }

/-- Ordinary scalar gradient settling. -/
noncomputable def plainQuadraticStep
    (rate curvature state : ℝ) : ℝ :=
  (1 - rate * curvature) * state

/-- Momentum zero computes exactly the plain current-state update. -/
@[simp] theorem momentumQuadraticStep_zero_current
    (rate curvature : ℝ) (state : MomentumState) :
    (momentumQuadraticStep rate curvature 0 state).current =
      plainQuadraticStep rate curvature state.current := by
  simp [momentumQuadraticStep, plainQuadraticStep]

/-- Plain settling on the slow eigenvalue `1` at the safe rate `1/9`. -/
noncomputable def plainSlowResidual (sweeps : ℕ) : ℝ :=
  (8 / 9 : ℝ) ^ sweeps

theorem plainSlowResidual_succ (sweeps : ℕ) :
    plainSlowResidual (sweeps + 1) =
      plainQuadraticStep (1 / 9) 1 (plainSlowResidual sweeps) := by
  simp [plainSlowResidual, plainQuadraticStep, pow_succ]
  ring

/-- Accelerated settling on the same slow mode, expressed as the actual
second-order recurrence induced by rate `1/9` and momentum `1/2`. -/
noncomputable def acceleratedSlowResidual : ℕ → ℝ
  | 0 => 1
  | 1 => 8 / 9
  | sweeps + 2 =>
      (4 / 3) * acceleratedSlowResidual (sweeps + 1) -
        (4 / 9) * acceleratedSlowResidual sweeps

theorem acceleratedSlowResidual_is_momentum_step (sweeps : ℕ) :
    momentumQuadraticStep (1 / 9) 1 (1 / 2)
      ⟨acceleratedSlowResidual sweeps,
        acceleratedSlowResidual (sweeps + 1)⟩ =
      ⟨acceleratedSlowResidual (sweeps + 1),
        acceleratedSlowResidual (sweeps + 2)⟩ := by
  apply MomentumState.ext
  · rfl
  · simp [momentumQuadraticStep, acceleratedSlowResidual]
    ring

/-- Exact residual formula for the accelerated slow mode.  It exposes the
geometric factor `2/3 = 1 - sqrt(1/9)` without hiding the repeated-root
polynomial prefactor. -/
theorem acceleratedSlowResidual_closedForm (sweeps : ℕ) :
    acceleratedSlowResidual sweeps =
      (1 + (sweeps : ℝ) / 3) * (2 / 3 : ℝ) ^ sweeps := by
  induction sweeps using Nat.twoStepInduction with
  | zero => norm_num [acceleratedSlowResidual]
  | one => norm_num [acceleratedSlowResidual]
  | more sweeps previous current =>
      rw [acceleratedSlowResidual, previous, current]
      push_cast
      rw [pow_add, pow_add]
      norm_num
      ring

/-- At four sweeps, the certified accelerated slow-mode residual is already
strictly smaller than the plain residual under the same per-sweep curvature
oracle. -/
theorem acceleratedSlowResidual_four_lt_plain :
    acceleratedSlowResidual 4 < plainSlowResidual 4 := by
  rw [acceleratedSlowResidual_closedForm]
  norm_num [plainSlowResidual]

/-- The high eigenmode is annihilated by the `1/L` factor, independently of
the extrapolated point. -/
theorem highMode_is_annihilated (state : MomentumState) :
    (momentumQuadraticStep (1 / 9) 9 (1 / 2) state).current = 0 := by
  simp [momentumQuadraticStep]

/-! ## Boundaries excluded by the positive theorem -/

/-- An inexact oracle adds a declared disturbance after the exact momentum
step. -/
noncomputable def inexactMomentumQuadraticStep
    (rate curvature momentum oracleError : ℝ)
    (state : MomentumState) : MomentumState :=
  let exact := momentumQuadraticStep rate curvature momentum state
  { exact with current := exact.current + oracleError }

@[simp] theorem inexactMomentumQuadraticStep_zero
    (rate curvature momentum : ℝ) (state : MomentumState) :
    inexactMomentumQuadraticStep rate curvature momentum 0 state =
      momentumQuadraticStep rate curvature momentum state := by
  simp [inexactMomentumQuadraticStep]

/-- Accumulated displacement from a constant inexact-oracle term after the
two exact bootstrap residuals of the scalar accelerated recurrence. -/
noncomputable def constantOracleDrift (oracleError : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | sweeps + 2 =>
      (4 / 3) * constantOracleDrift oracleError (sweeps + 1) -
        (4 / 9) * constantOracleDrift oracleError sweeps + oracleError

/-- Constant oracle error is amplified by the accelerated recurrence toward
the explicit coefficient `9`; it cannot be omitted from a rate certificate. -/
theorem constantOracleDrift_closedForm (oracleError : ℝ) (sweeps : ℕ) :
    constantOracleDrift oracleError sweeps =
      9 * oracleError *
        (1 - (1 + (sweeps : ℝ) / 2) * (2 / 3 : ℝ) ^ sweeps) := by
  induction sweeps using Nat.twoStepInduction with
  | zero => norm_num [constantOracleDrift]
  | one => norm_num [constantOracleDrift]
  | more sweeps previous current =>
      rw [constantOracleDrift, previous, current]
      push_cast
      rw [pow_add, pow_add]
      norm_num
      ring

/-- The first accumulated oracle disturbance appears exactly after the two
bootstrap entries. -/
@[simp] theorem constantOracleDrift_two (oracleError : ℝ) :
    constantOracleDrift oracleError 2 = oracleError := by
  norm_num [constantOracleDrift]

/-- Nonzero persistent oracle error moves the exact optimum immediately, so an
exact rate theorem cannot be applied without an error-floor term. -/
theorem persistentOracleError_moves_optimum (oracleError : ℝ)
    (nonzero : oracleError ≠ 0) :
    (inexactMomentumQuadraticStep (1 / 9) 1 (1 / 2) oracleError
      ⟨0, 0⟩).current ≠ 0 := by
  simpa [inexactMomentumQuadraticStep, momentumQuadraticStep] using nonzero

/-- Negative curvature makes the momentum-zero specialization expand even
though the nominal step size and penalty precision are positive. -/
theorem negativeCurvature_expands_without_dominance :
    |(momentumQuadraticStep 1 (-1) 0 ⟨1, 1⟩).current| = 2 := by
  norm_num [momentumQuadraticStep]

#print axioms strongConvexOn_add_precision
#print axioms strictConvexOn_add_precision
#print axioms scalarQuadratic_strongConvexOn
#print axioms positivePrecision_alone_not_sufficient
#print axioms momentumQuadraticStep_zero_current
#print axioms acceleratedSlowResidual_is_momentum_step
#print axioms acceleratedSlowResidual_closedForm
#print axioms acceleratedSlowResidual_four_lt_plain
#print axioms highMode_is_annihilated
#print axioms inexactMomentumQuadraticStep_zero
#print axioms constantOracleDrift_closedForm
#print axioms constantOracleDrift_two
#print axioms persistentOracleError_moves_optimum
#print axioms negativeCurvature_expands_without_dominance

end ConditionalAcceleration

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
