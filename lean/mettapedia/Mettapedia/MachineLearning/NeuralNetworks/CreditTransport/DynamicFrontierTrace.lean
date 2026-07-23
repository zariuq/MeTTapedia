import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActiveFrontierSettling

/-!
# Dynamic active-frontier traces

An active coordinate set may change after every settling sweep.  The safe
run-level object is therefore not one permanent mask, but a sequence of exact
directions, sparse directions, norm-error radii, task upper models, and
accepted transitions.

This module composes those per-sweep certificates.  It does not infer a
uniform smoothness constant from sampled Hessians, and it does not identify
energy monotonicity with task-loss descent.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace DynamicFrontierTrace

open scoped InnerProductSpace
open DirectionalTaskDescent

noncomputable section

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-- A changing-frontier run with enough analytic data to certify every
finite task step.  The frontier direction may have unrelated support at
successive rounds. -/
structure Certificate (loss : Parameter → ℝ) where
  parameter : ℕ → Parameter
  exactDirection : ℕ → Parameter
  frontierDirection : ℕ → Parameter
  beta : ℕ → ℝ
  error : ℕ → ℝ
  step : ℕ → ℝ
  upperModel : ∀ round,
    HasSmoothTaskUpperModelAt loss (parameter round)
      (exactDirection round) (beta round)
  frontierError : ∀ round,
    ‖frontierDirection round - exactDirection round‖ ≤ error round
  beta_nonneg : ∀ round, 0 ≤ beta round
  step_pos : ∀ round, 0 < step round
  error_relative : ∀ round, error round < ‖exactDirection round‖
  trust : ∀ round,
    beta round * step round *
        (‖exactDirection round‖ + error round) ^ 2 / 2 <
      ‖exactDirection round‖ *
        (‖exactDirection round‖ - error round)
  next_parameter : ∀ round,
    parameter (round + 1) =
      parameter round - step round • frontierDirection round

/-- Every certified changing-frontier sweep strictly decreases task loss. -/
theorem Certificate.step_strictTaskDescent
    {loss : Parameter → ℝ} (certificate : Certificate loss) (round : ℕ) :
    loss (certificate.parameter (round + 1)) <
      loss (certificate.parameter round) := by
  rw [certificate.next_parameter round]
  exact smoothTask_strict_descent_of_norm_error
    (certificate.upperModel round)
    (certificate.frontierError round)
    (certificate.beta_nonneg round)
    (certificate.step_pos round)
    (certificate.error_relative round)
    (certificate.trust round)

/-- Any positive-length prefix of a certified changing-frontier run has lower
task loss than its initial state. -/
theorem Certificate.loss_lt_initial_of_pos
    {loss : Parameter → ℝ} (certificate : Certificate loss)
    {rounds : ℕ} (positive : 0 < rounds) :
    loss (certificate.parameter rounds) <
      loss (certificate.parameter 0) := by
  induction rounds with
  | zero =>
      omega
  | succ rounds inductionHypothesis =>
      by_cases hzero : rounds = 0
      · subst rounds
        simpa using certificate.step_strictTaskDescent 0
      · exact lt_trans
          (by
            simpa [Nat.succ_eq_add_one] using
              certificate.step_strictTaskDescent rounds)
          (inductionHypothesis (Nat.pos_of_ne_zero hzero))

/-! ## Scalar positive and negative fixtures -/

noncomputable def scalarQuadraticLoss (parameter : ℝ) : ℝ :=
  parameter ^ 2 / 2

theorem scalarQuadratic_upperModel (parameter : ℝ) :
    HasSmoothTaskUpperModelAt scalarQuadraticLoss parameter parameter 1 := by
  intro direction step _hstep
  simp only [scalarQuadraticLoss, smul_eq_mul, Real.inner_apply,
    Real.norm_eq_abs, sq_abs]
  ring_nf
  exact le_rfl

noncomputable def halvingParameter (round : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ round

/-- Exact credit with a changing run index and zero approximation error. -/
noncomputable def halvingTrace : Certificate scalarQuadraticLoss where
  parameter := halvingParameter
  exactDirection := halvingParameter
  frontierDirection := halvingParameter
  beta := fun _ ↦ 1
  error := fun _ ↦ 0
  step := fun _ ↦ 1 / 2
  upperModel := by
    intro round
    exact scalarQuadratic_upperModel (halvingParameter round)
  frontierError := by
    intro round
    simp
  beta_nonneg := by
    intro round
    norm_num
  step_pos := by
    intro round
    norm_num
  error_relative := by
    intro round
    simp only [halvingParameter, Real.norm_eq_abs]
    positivity
  trust := by
    intro round
    have hpositive : 0 < |halvingParameter round| := by
      simp only [halvingParameter]
      positivity
    simp only [Real.norm_eq_abs]
    nlinarith [sq_pos_of_pos hpositive]
  next_parameter := by
    intro round
    simp only [halvingParameter, pow_succ, smul_eq_mul]
    ring

theorem halvingTrace_loss_strictly_decreases (round : ℕ) :
    scalarQuadraticLoss (halvingParameter (round + 1)) <
      scalarQuadraticLoss (halvingParameter round) :=
  halvingTrace.step_strictTaskDescent round

/-- Negative boundary: a stale zero frontier with unit error against a unit
exact direction cannot satisfy the strict relative-error gate. -/
theorem staleZeroFrontier_fails_relative_gate :
    ¬ (1 : ℝ) < ‖(1 : ℝ)‖ := by
  norm_num

#print axioms Certificate.step_strictTaskDescent
#print axioms Certificate.loss_lt_initial_of_pos
#print axioms halvingTrace_loss_strictly_decreases
#print axioms staleZeroFrontier_fails_relative_gate

end

end DynamicFrontierTrace

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
