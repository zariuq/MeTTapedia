import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization

/-!
# Supervised scalar primal-dual stability

This file derives the exact two-coordinate matrix induced by one in-place
primal step followed by one dual step on a supervised quadratic singular mode.
It proves the trace, determinant, and three Jury expressions and retains
positive and negative exact-rational fixtures.  Strict Jury conditions are
kept distinct from one-step Euclidean contraction: a non-normal stable fixture
has all three Jury quantities positive while amplifying a witness in one step.

The scalar analysis is not promoted to a nonlinear-network stability claim.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PrimalDualStability

/-- Parameters of one supervised scalar singular mode. -/
structure SupervisedScalarMode where
  primalRate : ℝ
  taskCurvature : ℝ
  singularValue : ℝ
  penalty : ℝ
  dualRate : ℝ
  dualLeak : ℝ

noncomputable def primalFactor (mode : SupervisedScalarMode) : ℝ :=
  1 - mode.primalRate *
    (mode.taskCurvature + mode.penalty * mode.singularValue ^ 2)

noncomputable def matrix00 (mode : SupervisedScalarMode) : ℝ :=
  primalFactor mode

noncomputable def matrix01 (mode : SupervisedScalarMode) : ℝ :=
  -mode.primalRate * mode.singularValue

noncomputable def matrix10 (mode : SupervisedScalarMode) : ℝ :=
  mode.dualRate * mode.singularValue * primalFactor mode

noncomputable def matrix11 (mode : SupervisedScalarMode) : ℝ :=
  1 - mode.dualRate * mode.dualLeak -
    mode.dualRate * mode.primalRate * mode.singularValue ^ 2

/-- Direct in-place primal-then-dual update. -/
noncomputable def supervisedPrimalDualStep
    (mode : SupervisedScalarMode) (state : ℝ × ℝ) : ℝ × ℝ :=
  let nextPrimal := state.1 - mode.primalRate *
    (mode.taskCurvature * state.1 + mode.singularValue * state.2 +
      mode.penalty * mode.singularValue ^ 2 * state.1)
  let nextDual := state.2 + mode.dualRate *
    (mode.singularValue * nextPrimal - mode.dualLeak * state.2)
  (nextPrimal, nextDual)

/-- The explicit matrix is exactly the declared in-place update. -/
theorem supervisedPrimalDualStep_eq_matrix
    (mode : SupervisedScalarMode) (state : ℝ × ℝ) :
    supervisedPrimalDualStep mode state =
      (matrix00 mode * state.1 + matrix01 mode * state.2,
        matrix10 mode * state.1 + matrix11 mode * state.2) := by
  simp [supervisedPrimalDualStep, matrix00, matrix01, matrix10, matrix11,
    primalFactor]
  constructor <;> ring

noncomputable def modeTrace (mode : SupervisedScalarMode) : ℝ :=
  matrix00 mode + matrix11 mode

noncomputable def modeDeterminant (mode : SupervisedScalarMode) : ℝ :=
  matrix00 mode * matrix11 mode - matrix01 mode * matrix10 mode

noncomputable def modeDiscriminant (mode : SupervisedScalarMode) : ℝ :=
  modeTrace mode ^ 2 - 4 * modeDeterminant mode

theorem modeTrace_expansion (mode : SupervisedScalarMode) :
    modeTrace mode =
      primalFactor mode + 1 - mode.dualRate * mode.dualLeak -
        mode.dualRate * mode.primalRate * mode.singularValue ^ 2 := by
  simp [modeTrace, matrix00, matrix11]
  ring

/-- The cancellation caused by consuming the new primal state leaves a simple
determinant factorization. -/
theorem modeDeterminant_factorization (mode : SupervisedScalarMode) :
    modeDeterminant mode =
      primalFactor mode * (1 - mode.dualRate * mode.dualLeak) := by
  simp [modeDeterminant, matrix00, matrix01, matrix10, matrix11]
  ring

noncomputable def juryFirst (mode : SupervisedScalarMode) : ℝ :=
  1 - modeDeterminant mode

noncomputable def jurySecond (mode : SupervisedScalarMode) : ℝ :=
  1 - modeTrace mode + modeDeterminant mode

noncomputable def juryThird (mode : SupervisedScalarMode) : ℝ :=
  1 + modeTrace mode + modeDeterminant mode

def StrictJury (mode : SupervisedScalarMode) : Prop :=
  0 < juryFirst mode ∧ 0 < jurySecond mode ∧ 0 < juryThird mode

theorem juryFirst_expansion (mode : SupervisedScalarMode) :
    juryFirst mode =
      mode.dualRate * mode.dualLeak +
        mode.primalRate *
          (mode.taskCurvature + mode.penalty * mode.singularValue ^ 2) -
        mode.primalRate *
          (mode.taskCurvature + mode.penalty * mode.singularValue ^ 2) *
          mode.dualRate * mode.dualLeak := by
  simp [juryFirst, modeDeterminant_factorization, primalFactor]
  ring

theorem jurySecond_expansion (mode : SupervisedScalarMode) :
    jurySecond mode =
      mode.dualRate * mode.primalRate *
        (mode.singularValue ^ 2 + mode.dualLeak *
          (mode.taskCurvature + mode.penalty * mode.singularValue ^ 2)) := by
  simp [jurySecond, modeTrace, modeDeterminant_factorization,
    matrix00, matrix11, primalFactor]
  ring

theorem juryThird_expansion (mode : SupervisedScalarMode) :
    juryThird mode =
      4 - 2 * mode.primalRate *
          (mode.taskCurvature + mode.penalty * mode.singularValue ^ 2) -
        2 * mode.dualRate * mode.dualLeak +
        mode.dualRate * mode.dualLeak * mode.primalRate *
          (mode.taskCurvature + mode.penalty * mode.singularValue ^ 2) -
        mode.dualRate * mode.primalRate * mode.singularValue ^ 2 := by
  simp [juryThird, modeTrace, modeDeterminant_factorization,
    matrix00, matrix11, primalFactor]
  ring

/-- At zero task curvature and zero leak, the third Jury quantity is exactly
the published constraint-mode boundary. -/
theorem constraintOnly_zeroLeak_juryThird
    (mode : SupervisedScalarMode)
    (hcurvature : mode.taskCurvature = 0) (hleak : mode.dualLeak = 0) :
    juryThird mode =
      4 - mode.primalRate * mode.singularValue ^ 2 *
        (2 * mode.penalty + mode.dualRate) := by
  rw [juryThird_expansion]
  simp [hcurvature, hleak]
  ring

/-! ## Exact positive and negative modes -/

noncomputable def stableRealMode : SupervisedScalarMode where
  primalRate := 1 / 4
  taskCurvature := 1
  singularValue := 1
  penalty := 1
  dualRate := 1 / 8
  dualLeak := 0

noncomputable def stableOscillatoryMode : SupervisedScalarMode where
  primalRate := 1 / 4
  taskCurvature := 1
  singularValue := 1
  penalty := 1
  dualRate := 1 / 2
  dualLeak := 0

theorem stableRealMode_strictJury : StrictJury stableRealMode := by
  norm_num [StrictJury, juryFirst, jurySecond, juryThird, modeTrace,
    modeDeterminant, matrix00, matrix01, matrix10, matrix11, primalFactor,
    stableRealMode]

theorem stableRealMode_realDiscriminant :
    0 < modeDiscriminant stableRealMode := by
  norm_num [modeDiscriminant, modeTrace, modeDeterminant, matrix00, matrix01,
    matrix10, matrix11, primalFactor, stableRealMode]

theorem stableOscillatoryMode_strictJury : StrictJury stableOscillatoryMode := by
  norm_num [StrictJury, juryFirst, jurySecond, juryThird, modeTrace,
    modeDeterminant, matrix00, matrix01, matrix10, matrix11, primalFactor,
    stableOscillatoryMode]

theorem stableOscillatoryMode_negativeDiscriminant :
    modeDiscriminant stableOscillatoryMode < 0 := by
  norm_num [modeDiscriminant, modeTrace, modeDeterminant, matrix00, matrix01,
    matrix10, matrix11, primalFactor, stableOscillatoryMode]

noncomputable def constraintOnlyStableMode : SupervisedScalarMode where
  primalRate := 1 / 2
  taskCurvature := 0
  singularValue := 1
  penalty := 1
  dualRate := 1
  dualLeak := 0

noncomputable def curvatureUnstableMode : SupervisedScalarMode :=
  { constraintOnlyStableMode with taskCurvature := 3 }

theorem constraintOnlyStableMode_strictJury :
    StrictJury constraintOnlyStableMode := by
  norm_num [StrictJury, juryFirst, jurySecond, juryThird, modeTrace,
    modeDeterminant, matrix00, matrix01, matrix10, matrix11, primalFactor,
    constraintOnlyStableMode]

/-- Adding supervised curvature at unchanged rates can cross the third Jury
boundary even when the constraint-only mode passes it. -/
theorem curvatureUnstableMode_not_strictJury :
    ¬ StrictJury curvatureUnstableMode := by
  norm_num [StrictJury, juryFirst, jurySecond, juryThird, modeTrace,
    modeDeterminant, matrix00, matrix01, matrix10, matrix11, primalFactor,
    curvatureUnstableMode, constraintOnlyStableMode]

noncomputable def zeroDualRateMode : SupervisedScalarMode where
  primalRate := 1 / 4
  taskCurvature := 1
  singularValue := 1
  penalty := 1
  dualRate := 0
  dualLeak := 1

/-- A contracting primal block does not remove the frozen multiplier's unit
mode: the second Jury quantity is exactly zero. -/
theorem zeroDualRateMode_not_strictJury : ¬ StrictJury zeroDualRateMode := by
  norm_num [StrictJury, juryFirst, jurySecond, juryThird, modeTrace,
    modeDeterminant, matrix00, matrix01, matrix10, matrix11, primalFactor,
    zeroDualRateMode]

noncomputable def nonnormalTransientMode : SupervisedScalarMode where
  primalRate := 1 / 8
  taskCurvature := 1 / 8
  singularValue := 1
  penalty := 1 / 8
  dualRate := 1 / 4
  dualLeak := 0

theorem nonnormalTransientMode_strictJury :
    StrictJury nonnormalTransientMode := by
  norm_num [StrictJury, juryFirst, jurySecond, juryThird, modeTrace,
    modeDeterminant, matrix00, matrix01, matrix10, matrix11, primalFactor,
    nonnormalTransientMode]

noncomputable def pairSquaredNorm (state : ℝ × ℝ) : ℝ :=
  state.1 ^ 2 + state.2 ^ 2

theorem nonnormalTransientMode_witness_step :
    supervisedPrimalDualStep nonnormalTransientMode (1, 1) =
      (27 / 32, 155 / 128) := by
  norm_num [supervisedPrimalDualStep, nonnormalTransientMode]

/-- Strict Jury stability does not imply one-step Euclidean contraction. -/
theorem nonnormalTransientMode_amplifies_oneStep :
    pairSquaredNorm (1, 1) <
      pairSquaredNorm
        (supervisedPrimalDualStep nonnormalTransientMode (1, 1)) := by
  rw [nonnormalTransientMode_witness_step]
  norm_num [pairSquaredNorm]

/-! ## Local nonlinear and moving-target boundary -/

/-- A reusable scalar quadratic remainder model for a locally linearized
credit solver. -/
noncomputable def scalarQuadraticErrorMap (linear remainder state : ℝ) : ℝ :=
  linear * state + remainder * state ^ 2

/-- The local error map used by the exact-rational conformance fixture. -/
noncomputable def localQuadraticErrorMap (state : ℝ) : ℝ :=
  scalarQuadraticErrorMap (1 / 4) (1 / 4) state

theorem hasDerivAt_localQuadraticErrorMap (state : ℝ) :
    HasDerivAt localQuadraticErrorMap (1 / 4 + state / 2) state := by
  unfold localQuadraticErrorMap scalarQuadraticErrorMap
  convert!
    ((hasDerivAt_id state).const_mul (1 / 4 : ℝ)).add
      ((hasDerivAt_pow 2 state).const_mul (1 / 4 : ℝ)) using 1;
    ring

/-- The declared unit neighborhood is invariant with a strict half-radius
image bound. -/
theorem localQuadraticErrorMap_maps_unitBall_to_halfBall
    (state : ℝ) (hstate : |state| ≤ 1) :
    |localQuadraticErrorMap state| ≤ 1 / 2 := by
  rcases abs_le.mp hstate with ⟨hlower, hupper⟩
  have hproduct : 0 ≤ (1 - state) * (1 + state) :=
    mul_nonneg (by linarith) (by linarith)
  rw [abs_le]
  constructor
  · simp [localQuadraticErrorMap, scalarQuadraticErrorMap]
    nlinarith [sq_nonneg (state + 1 / 2)]
  · simp [localQuadraticErrorMap, scalarQuadraticErrorMap]
    nlinarith

/-- On the same unit neighborhood the derivative magnitude is at most 3/4,
so the local map is contractive there. -/
theorem localQuadraticErrorMap_derivative_abs_le
    (state : ℝ) (hstate : |state| ≤ 1) :
    |1 / 4 + state / 2| ≤ 3 / 4 := by
  rcases abs_le.mp hstate with ⟨hlower, hupper⟩
  rw [abs_le]
  constructor <;> linarith

theorem localQuadraticErrorMap_boundary_value :
    localQuadraticErrorMap 1 = 1 / 2 := by
  norm_num [localQuadraticErrorMap, scalarQuadraticErrorMap]

/-- A target displacement of one quarter remains inside the unit tracking
ball for the worst positive boundary state. -/
theorem localQuadraticErrorMap_safeDrift :
    |localQuadraticErrorMap 1 + 1 / 4| = 3 / 4 := by
  norm_num [localQuadraticErrorMap, scalarQuadraticErrorMap]

/-- A larger target displacement can leave the certified neighborhood in one
step, even though the unshifted map is locally contractive. -/
theorem localQuadraticErrorMap_excessiveDrift :
    1 < |localQuadraticErrorMap 1 + 3 / 4| := by
  norm_num [localQuadraticErrorMap, scalarQuadraticErrorMap]

/-- The local contraction cannot be globalized: state four expands to five. -/
theorem localQuadraticErrorMap_globalExpansion :
    localQuadraticErrorMap 4 = 5 ∧ |(4 : ℝ)| < |localQuadraticErrorMap 4| := by
  norm_num [localQuadraticErrorMap, scalarQuadraticErrorMap]

#print axioms supervisedPrimalDualStep_eq_matrix
#print axioms modeDeterminant_factorization
#print axioms jurySecond_expansion
#print axioms constraintOnly_zeroLeak_juryThird
#print axioms curvatureUnstableMode_not_strictJury
#print axioms nonnormalTransientMode_amplifies_oneStep
#print axioms localQuadraticErrorMap_maps_unitBall_to_halfBall
#print axioms localQuadraticErrorMap_derivative_abs_le
#print axioms localQuadraticErrorMap_excessiveDrift
#print axioms localQuadraticErrorMap_globalExpansion

end PrimalDualStability

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
