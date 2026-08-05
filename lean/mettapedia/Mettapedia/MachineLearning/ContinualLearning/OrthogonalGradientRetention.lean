import Mettapedia.MachineLearning.ContinualLearning.MinimumChangeUpdate
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Orthogonal-gradient retention across a task sequence

Bennani, Doan, and Sugiyama, *Generalisation Guarantees for Continual
Learning with Orthogonal Gradient Descent* (2020), Theorem 2, prove
no-forgetting on stored examples in the neural-tangent linearization when all
later updates are orthogonal to the stored Jacobian.

This file isolates and strengthens that algebraic core.  It proves exact
retention for an arbitrary finite update sequence in a real inner-product
space, an approximate bound in terms of Jacobian drift and total path length,
and a nonlinear counterexample showing why first-order orthogonality alone
does not imply finite functional retention outside the fixed-Jacobian model.

The result complements `MinimumChangeUpdate`, which constructs and
characterizes orthogonal projections, and `RetentionSafeUpdate`, which gives
finite nonlinear trust-region conditions.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

open scoped InnerProductSpace

variable {Parameter : Type*} [NormedAddCommGroup Parameter]
  [InnerProductSpace ℝ Parameter]

/-- Sum of a finite sequence of parameter updates, in execution order. -/
def totalUpdate : List Parameter → Parameter
  | [] => 0
  | update :: updates => update + totalUpdate updates

/-- Parameter reached after applying a finite additive update sequence. -/
def accumulatedParameter
    (initial : Parameter) (updates : List Parameter) : Parameter :=
  initial + totalUpdate updates

/-- Change of a fixed-Jacobian scalar prediction along a finite update
sequence. -/
noncomputable def linearizedRetentionChange
    (jacobian : Parameter) : List Parameter → ℝ
  | [] => 0
  | update :: updates =>
      ⟪jacobian, update⟫_ℝ +
        linearizedRetentionChange jacobian updates

/-- Total parameter-space path length of the update sequence. -/
noncomputable def updatePathLength : List Parameter → ℝ
  | [] => 0
  | update :: updates => ‖update‖ + updatePathLength updates

/-- A scalar readout in the fixed-Jacobian, neural-tangent linearization
anchored at `initial`. -/
noncomputable def linearizedReadout
    (base : ℝ) (jacobian initial parameter : Parameter) : ℝ :=
  base + ⟪jacobian, parameter - initial⟫_ℝ

/-- The fixed-Jacobian readout change is exactly the sum of the per-update
directional derivatives. -/
theorem inner_totalUpdate_eq_linearizedRetentionChange
    (jacobian : Parameter) :
    ∀ updates : List Parameter,
      ⟪jacobian, totalUpdate updates⟫_ℝ =
        linearizedRetentionChange jacobian updates := by
  intro updates
  induction updates with
  | nil =>
      simp [totalUpdate, linearizedRetentionChange]
  | cons update updates inductionHypothesis =>
      simp [totalUpdate, linearizedRetentionChange, inner_add_right,
        inductionHypothesis]

/-- Source correspondence: the prediction after the finite sequence is its
initial value plus the recursively accumulated routed derivative. -/
theorem linearizedReadout_accumulated
    (base : ℝ) (jacobian initial : Parameter)
    (updates : List Parameter) :
    linearizedReadout base jacobian initial
        (accumulatedParameter initial updates) =
      base + linearizedRetentionChange jacobian updates := by
  rw [linearizedReadout, accumulatedParameter]
  have hsub :
      initial + totalUpdate updates - initial = totalUpdate updates := by
    abel
  rw [hsub, inner_totalUpdate_eq_linearizedRetentionChange]

/-- Exact no-forgetting theorem: if every later update is orthogonal to the
stored Jacobian, the stored linearized prediction is unchanged. -/
theorem linearizedReadout_no_forgetting
    (base : ℝ) (jacobian initial : Parameter)
    (updates : List Parameter)
    (orthogonal : ∀ update ∈ updates, ⟪jacobian, update⟫_ℝ = 0) :
    linearizedReadout base jacobian initial
        (accumulatedParameter initial updates) = base := by
  rw [linearizedReadout_accumulated]
  have hchange : linearizedRetentionChange jacobian updates = 0 := by
    induction updates with
    | nil =>
        simp [linearizedRetentionChange]
    | cons update updates inductionHypothesis =>
        have hhead : ⟪jacobian, update⟫_ℝ = 0 :=
          orthogonal update (by simp)
        have htail :
            ∀ later ∈ updates, ⟪jacobian, later⟫_ℝ = 0 := by
          intro later laterMem
          exact orthogonal later (by simp [laterMem])
        simp [linearizedRetentionChange, hhead,
          inductionHypothesis htail]
  rw [hchange, add_zero]

/-- Cauchy--Schwarz turns a fixed Jacobian and update path into a cumulative
linearized-retention bound. -/
theorem linearizedRetentionChange_abs_le_norm_mul_pathLength
    (jacobian : Parameter) :
    ∀ updates : List Parameter,
      |linearizedRetentionChange jacobian updates| ≤
        ‖jacobian‖ * updatePathLength updates := by
  intro updates
  induction updates with
  | nil =>
      simp [linearizedRetentionChange, updatePathLength]
  | cons update updates inductionHypothesis =>
      rw [linearizedRetentionChange, updatePathLength]
      calc
        |⟪jacobian, update⟫_ℝ +
            linearizedRetentionChange jacobian updates| ≤
            |⟪jacobian, update⟫_ℝ| +
              |linearizedRetentionChange jacobian updates| :=
          abs_add_le _ _
        _ ≤ ‖jacobian‖ * ‖update‖ +
              ‖jacobian‖ * updatePathLength updates :=
          add_le_add (abs_real_inner_le_norm jacobian update)
            inductionHypothesis
        _ = ‖jacobian‖ *
              (‖update‖ + updatePathLength updates) := by ring

/-- If every update is orthogonal to the stored Jacobian, evaluating with a
drifted actual Jacobian is equivalent to evaluating only the Jacobian drift. -/
theorem linearizedRetentionChange_eq_jacobianDrift
    (stored actual : Parameter) :
    ∀ updates : List Parameter,
      (∀ update ∈ updates, ⟪stored, update⟫_ℝ = 0) →
      linearizedRetentionChange actual updates =
        linearizedRetentionChange (actual - stored) updates := by
  intro updates orthogonal
  induction updates with
  | nil =>
      simp [linearizedRetentionChange]
  | cons update updates inductionHypothesis =>
      have hhead : ⟪stored, update⟫_ℝ = 0 :=
        orthogonal update (by simp)
      have htail :
          ∀ later ∈ updates, ⟪stored, later⟫_ℝ = 0 := by
        intro later laterMem
        exact orthogonal later (by simp [laterMem])
      rw [linearizedRetentionChange, linearizedRetentionChange,
        inductionHypothesis htail, inner_sub_left, hhead, sub_zero]

/-- Approximate no-forgetting under Jacobian drift.  The error is controlled
by the drift norm times the total update path length, rather than being
silently treated as zero. -/
theorem linearizedReadout_forgetting_le_jacobianDrift_mul_pathLength
    (base : ℝ) (stored actual initial : Parameter)
    (updates : List Parameter)
    (orthogonal : ∀ update ∈ updates, ⟪stored, update⟫_ℝ = 0) :
    |linearizedReadout base actual initial
          (accumulatedParameter initial updates) - base| ≤
      ‖actual - stored‖ * updatePathLength updates := by
  rw [linearizedReadout_accumulated]
  simp only [add_sub_cancel_left]
  rw [linearizedRetentionChange_eq_jacobianDrift stored actual updates orthogonal]
  exact linearizedRetentionChange_abs_le_norm_mul_pathLength
    (actual - stored) updates

/-! ## Positive and negative fixtures -/

/-- A two-coordinate stored feature and a sequence confined to its orthogonal
coordinate satisfy exact no-forgetting. -/
theorem twoCoordinate_orthogonal_sequence_preserves_readout :
    linearizedReadout (7 : ℝ) (1 : ℂ) 0
        (accumulatedParameter 0
          [(2 : ℝ) • Complex.I, (-3 : ℝ) • Complex.I]) = 7 := by
  apply linearizedReadout_no_forgetting
  intro update updateMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at updateMem
  rcases updateMem with rfl | rfl <;> norm_num

/-- A first-order stationary point does not make an arbitrary finite update
safe for a nonlinear readout. -/
def nonlinearQuadraticReadout (parameter : ℝ) : ℝ :=
  parameter ^ 2

theorem nonlinear_stationary_gradient_does_not_imply_no_forgetting :
    HasDerivAt nonlinearQuadraticReadout 0 0 ∧
      nonlinearQuadraticReadout (0 + 1) ≠
        nonlinearQuadraticReadout 0 := by
  constructor
  · unfold nonlinearQuadraticReadout
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  · norm_num [nonlinearQuadraticReadout]

#print axioms linearizedReadout_no_forgetting
#print axioms linearizedReadout_forgetting_le_jacobianDrift_mul_pathLength
#print axioms twoCoordinate_orthogonal_sequence_preserves_readout
#print axioms nonlinear_stationary_gradient_does_not_imply_no_forgetting

end Mettapedia.MachineLearning.ContinualLearning
