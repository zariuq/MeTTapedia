import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FixedPointSensitivity

/-!
# Fixed-point sensitivity of an actual scalar primal-dual cycle

This file instantiates the abstract sensitivity theorem on the existing
primal-then-dual transition, rather than on a new surrogate recurrence.  The
chosen positive-leak mode is globally contractive in the product sup norm.
Its target-dependent equilibrium is nonzero and moves with the supervised
target, so the resulting parameter-sensitivity theorem is substantive.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PrimalDualFixedPointSensitivity

open AmortizedInitialization
open FixedPointSensitivity
open Instances

/-- Project one enabled primal-then-dual cycle of the existing transition to
its mutable primal and dual coordinates. -/
noncomputable def primalDualCyclePair
    (problem : ScalarPrimalDualProblem) (prediction : ℝ)
    (state : ℝ × ℝ) : ℝ × ℝ :=
  let initial : PrimalDualState :=
    { phase := .ready, primal := state.1, dual := state.2, update := 0 }
  let afterPrimal :=
    primalDualTransition problem prediction .primalStep initial
  let afterDual :=
    primalDualTransition problem prediction .dualStep afterPrimal
  (afterDual.primal, afterDual.dual)

/-- A stable positive-leak member of the implemented scalar family. -/
noncomputable def trackedLeakyProblem (target : ℝ) :
    ScalarPrimalDualProblem where
  target := target
  penalty := 1
  primalRate := 1 / 4
  dualRate := 1 / 8
  dualLeak := 4
  initialDual := 0

noncomputable def trackedLeakySolver (target : ℝ) (state : ℝ × ℝ) :
    ℝ × ℝ :=
  primalDualCyclePair (trackedLeakyProblem target) 0 state

/-- The exact equilibrium obtained from the continuation equations for
penalty one, leak four, and prediction zero. -/
noncomputable def trackedLeakyTarget (target : ℝ) : ℝ × ℝ :=
  (4 * target / 9, target / 9)

theorem trackedLeakySolver_expansion (target : ℝ) (state : ℝ × ℝ) :
    trackedLeakySolver target state =
      (state.1 / 2 - state.2 / 4 + target / 4,
        state.1 / 16 + 15 * state.2 / 32 + target / 32) := by
  simp [trackedLeakySolver, primalDualCyclePair, trackedLeakyProblem,
    primalDualTransition, scalarPrimalGradient]
  constructor <;> ring

theorem trackedLeakyTarget_fixed (target : ℝ) :
    IsFixedPoint (trackedLeakySolver target) (trackedLeakyTarget target) := by
  rw [IsFixedPoint, trackedLeakySolver_expansion]
  apply Prod.ext <;> simp [trackedLeakyTarget] <;> ring

/-- The actual two-coordinate cycle is a three-quarter contraction in the
product sup norm. -/
theorem trackedLeakySolver_pair_distance_le
    (target : ℝ) (left right : ℝ × ℝ) :
    ‖trackedLeakySolver target left - trackedLeakySolver target right‖ ≤
      (3 / 4 : ℝ) * ‖left - right‖ := by
  rw [trackedLeakySolver_expansion, trackedLeakySolver_expansion]
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  let dx := left.1 - right.1
  let dy := left.2 - right.2
  let bound := max |dx| |dy|
  have hfirstRewrite :
      left.1 / 2 - left.2 / 4 + target / 4 -
          (right.1 / 2 - right.2 / 4 + target / 4) =
        dx / 2 - dy / 4 := by
    simp [dx]
    ring
  have hsecondRewrite :
      left.1 / 16 + 15 * left.2 / 32 + target / 32 -
          (right.1 / 16 + 15 * right.2 / 32 + target / 32) =
        dx / 16 + 15 * dy / 32 := by
    simp [dx, dy]
    ring
  have hdx : |dx| ≤ bound := by
    exact le_max_left _ _
  have hdy : |dy| ≤ bound := by
    exact le_max_right _ _
  have hboundNonneg : 0 ≤ bound :=
    le_trans (abs_nonneg dx) hdx
  rcases (abs_le.mp hdx) with ⟨hdxLower, hdxUpper⟩
  rcases (abs_le.mp hdy) with ⟨hdyLower, hdyUpper⟩
  have hfirst : |dx / 2 - dy / 4| ≤ (3 / 4 : ℝ) * bound := by
    rw [abs_le]
    constructor <;> nlinarith
  have hsecond :
      |dx / 16 + 15 * dy / 32| ≤ (3 / 4 : ℝ) * bound := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [hfirstRewrite, hsecondRewrite]
  change max |dx / 2 - dy / 4| |dx / 16 + 15 * dy / 32| ≤
    (3 / 4 : ℝ) * bound
  exact max_le hfirst hsecond

noncomputable def trackedLeakyCertificate (target : ℝ) :
    ContractionCertificate (trackedLeakySolver target) where
  factor := 3 / 4
  factor_nonneg := by norm_num
  factor_lt_one := by norm_num
  contracts := trackedLeakySolver_pair_distance_le target

/-- Changing the supervised target changes one cycle, at the old equilibrium,
by at most one quarter of the target distance. -/
theorem trackedLeakySolver_change_at_oldTarget_le
    (previous next : ℝ) :
    ‖trackedLeakySolver previous (trackedLeakyTarget previous) -
        trackedLeakySolver next (trackedLeakyTarget previous)‖ ≤
      (1 / 4 : ℝ) * dist previous next := by
  rw [trackedLeakySolver_expansion, trackedLeakySolver_expansion]
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs,
    Real.dist_eq]
  have hfirst :
      (trackedLeakyTarget previous).1 / 2 -
            (trackedLeakyTarget previous).2 / 4 + previous / 4 -
          ((trackedLeakyTarget previous).1 / 2 -
            (trackedLeakyTarget previous).2 / 4 + next / 4) =
        (previous - next) / 4 := by
    ring
  have hsecond :
      (trackedLeakyTarget previous).1 / 16 +
            15 * (trackedLeakyTarget previous).2 / 32 + previous / 32 -
          ((trackedLeakyTarget previous).1 / 16 +
            15 * (trackedLeakyTarget previous).2 / 32 + next / 32) =
        (previous - next) / 32 := by
    ring
  rw [hfirst, hsecond]
  apply max_le
  · rw [abs_div]
    norm_num
    exact le_of_eq (by ring)
  · rw [abs_div]
    norm_num
    nlinarith [abs_nonneg (previous - next)]

/-- The abstract sensitivity theorem now bounds the equilibrium motion of the
implemented primal-dual cycle from its target-parameter motion. -/
theorem trackedLeakyTarget_drift_le_parameter_distance
    (previous next : ℝ) :
    ‖trackedLeakyTarget previous - trackedLeakyTarget next‖ ≤
      ((1 / 4 : ℝ) * dist previous next) /
        (1 - (trackedLeakyCertificate next).factor) := by
  exact global_target_drift_le_parameter_distance_div
    trackedLeakyCertificate trackedLeakyTarget_fixed previous next (1 / 4)
    (trackedLeakySolver_change_at_oldTarget_le previous next)

/-- This bound is meaningful rather than vacuous: the two equilibrium
coordinates both move when the supervised target moves. -/
theorem trackedLeakyTarget_zero_one_nonconstant :
    trackedLeakyTarget 0 ≠ trackedLeakyTarget 1 := by
  intro hequal
  have hfirst := congrArg Prod.fst hequal
  norm_num [trackedLeakyTarget] at hfirst

#print axioms trackedLeakySolver_expansion
#print axioms trackedLeakyTarget_fixed
#print axioms trackedLeakySolver_pair_distance_le
#print axioms trackedLeakySolver_change_at_oldTarget_le
#print axioms trackedLeakyTarget_drift_le_parameter_distance
#print axioms trackedLeakyTarget_zero_one_nonconstant

end PrimalDualFixedPointSensitivity

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
