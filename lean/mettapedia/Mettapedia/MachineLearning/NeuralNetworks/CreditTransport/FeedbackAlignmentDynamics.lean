import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.BroadcastProxy

/-!
# Feedback-alignment dynamics

Lillicrap et al., *Random Synaptic Feedback Weights Support Error Backpropagation
for Deep Learning* (arXiv:1411.0247), Supplementary Proof 1, analyze the
continuous-time two-layer linear feedback-alignment system.  Their key
conservation law is

`B W + Wᵀ Bᵀ = A Aᵀ + C`.

This file recovers the scalar dynamics exactly.  It derives the conserved
quantity's directional derivative, the exact error and loss velocities, and
the positive alignment product on the source's `C = 0` manifold.  It also
derives the exact finite-Euler invariant drift and error recurrence, exposing
the step-size boundary hidden by the continuous-time limit.

The results complement the existing one-step DFA credit-transport instance:
they explain when a fixed broadcast weight becomes a useful direction, without
identifying feedback alignment with backpropagation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FeedbackAlignmentDynamics

/-- Scalar two-layer linear network state: `hiddenWeight` is the source's
`A`, while `outputWeight` is its `W`. -/
structure ScalarFAState where
  hiddenWeight : ℝ
  outputWeight : ℝ

/-- Scalar prediction error `target - W A`. -/
def error (target : ℝ) (state : ScalarFAState) : ℝ :=
  target - state.outputWeight * state.hiddenWeight

/-- Continuous-time feedback-alignment velocity `Ȧ = B E`. -/
def hiddenVelocity
    (feedback target : ℝ) (state : ScalarFAState) : ℝ :=
  feedback * error target state

/-- Continuous-time output-weight velocity `Ẇ = E A`. -/
def outputVelocity (target : ℝ) (state : ScalarFAState) : ℝ :=
  error target state * state.hiddenWeight

/-- Scalar form of the source invariant:
`2 B W - A² = C`. -/
def alignmentInvariant
    (feedback : ℝ) (state : ScalarFAState) : ℝ :=
  2 * feedback * state.outputWeight - state.hiddenWeight ^ 2

/-- Error velocity obtained by differentiating `target - W A` along the
feedback-alignment vector field. -/
def errorVelocity
    (feedback target : ℝ) (state : ScalarFAState) : ℝ :=
  -(outputVelocity target state * state.hiddenWeight +
      state.outputWeight * hiddenVelocity feedback target state)

/-- Directional derivative of the half-squared error along the continuous
feedback-alignment vector field. -/
def lossVelocity
    (feedback target : ℝ) (state : ScalarFAState) : ℝ :=
  error target state * errorVelocity feedback target state

/-- Half-squared scalar task loss. -/
noncomputable def loss (target : ℝ) (state : ScalarFAState) : ℝ :=
  error target state ^ 2 / 2

/-- The source invariant has zero directional derivative along the exact
continuous-time feedback-alignment field. -/
theorem alignmentInvariant_directionalDerivative_eq_zero
    (feedback target : ℝ) (state : ScalarFAState) :
    2 * feedback * outputVelocity target state -
        2 * state.hiddenWeight *
          hiddenVelocity feedback target state =
      0 := by
  simp [outputVelocity, hiddenVelocity]
  ring

/-- Exact scalar error-velocity formula. -/
theorem errorVelocity_formula
    (feedback target : ℝ) (state : ScalarFAState) :
    errorVelocity feedback target state =
      -error target state *
        (state.hiddenWeight ^ 2 +
          feedback * state.outputWeight) := by
  simp [errorVelocity, outputVelocity, hiddenVelocity]
  ring

/-- Exact loss-velocity formula before using the invariant. -/
theorem lossVelocity_formula
    (feedback target : ℝ) (state : ScalarFAState) :
    lossVelocity feedback target state =
      -(error target state ^ 2 *
        (state.hiddenWeight ^ 2 +
          feedback * state.outputWeight)) := by
  rw [lossVelocity, errorVelocity_formula]
  ring

/-- On the source's `C = 0` manifold, loss velocity is a negative
sum-of-squares product. -/
theorem lossVelocity_eq_of_zeroInvariant
    (feedback target : ℝ) (state : ScalarFAState)
    (hzero : alignmentInvariant feedback state = 0) :
    lossVelocity feedback target state =
      -(3 / 2 : ℝ) * error target state ^ 2 *
        state.hiddenWeight ^ 2 := by
  rw [lossVelocity_formula]
  unfold alignmentInvariant at hzero
  nlinarith

/-- Continuous-time loss cannot increase on the zero-invariant manifold. -/
theorem lossVelocity_nonpos_of_zeroInvariant
    (feedback target : ℝ) (state : ScalarFAState)
    (hzero : alignmentInvariant feedback state = 0) :
    lossVelocity feedback target state ≤ 0 := by
  rw [lossVelocity_eq_of_zeroInvariant feedback target state hzero]
  nlinarith [sq_nonneg (error target state),
    sq_nonneg state.hiddenWeight,
    mul_nonneg (sq_nonneg (error target state))
      (sq_nonneg state.hiddenWeight)]

/-- The loss derivative is strictly negative when both the error and hidden
weight are nonzero. -/
theorem lossVelocity_neg_of_zeroInvariant
    (feedback target : ℝ) (state : ScalarFAState)
    (hzero : alignmentInvariant feedback state = 0)
    (herror : error target state ≠ 0)
    (hhidden : state.hiddenWeight ≠ 0) :
    lossVelocity feedback target state < 0 := by
  rw [lossVelocity_eq_of_zeroInvariant feedback target state hzero]
  have herrorSq := sq_pos_of_ne_zero herror
  have hhiddenSq := sq_pos_of_ne_zero hhidden
  have hproduct := mul_pos herrorSq hhiddenSq
  nlinarith

/-- Scalar inner product between the fixed-feedback hidden update and the
backprop hidden update. -/
def alignmentProduct
    (feedback target : ℝ) (state : ScalarFAState) : ℝ :=
  (feedback * error target state) *
    (state.outputWeight * error target state)

/-- On the zero-invariant manifold, feedback and backprop hidden updates have
an explicitly nonnegative product. -/
theorem alignmentProduct_eq_of_zeroInvariant
    (feedback target : ℝ) (state : ScalarFAState)
    (hzero : alignmentInvariant feedback state = 0) :
    alignmentProduct feedback target state =
      error target state ^ 2 * state.hiddenWeight ^ 2 / 2 := by
  unfold alignmentProduct
  unfold alignmentInvariant at hzero
  nlinarith [sq_nonneg (error target state)]

/-- Nonnegative feedback/backprop alignment on the source manifold. -/
theorem alignmentProduct_nonnegative_of_zeroInvariant
    (feedback target : ℝ) (state : ScalarFAState)
    (hzero : alignmentInvariant feedback state = 0) :
    0 ≤ alignmentProduct feedback target state := by
  rw [alignmentProduct_eq_of_zeroInvariant feedback target state hzero]
  positivity

/-! ## Exact finite-Euler boundary -/

/-- One simultaneous Euler step of the continuous feedback-alignment field. -/
def eulerStep
    (rate feedback target : ℝ)
    (state : ScalarFAState) : ScalarFAState where
  hiddenWeight :=
    state.hiddenWeight +
      rate * hiddenVelocity feedback target state
  outputWeight :=
    state.outputWeight +
      rate * outputVelocity target state

/-- Simultaneous Euler stepping does not preserve the continuous invariant:
it decreases it by an exact second-order term. -/
theorem euler_alignmentInvariant_drift
    (rate feedback target : ℝ) (state : ScalarFAState) :
    alignmentInvariant feedback (eulerStep rate feedback target state) =
      alignmentInvariant feedback state -
        rate ^ 2 * feedback ^ 2 * error target state ^ 2 := by
  simp [alignmentInvariant, eulerStep, hiddenVelocity, outputVelocity]
  ring

/-- Exact finite-step error recurrence, including the second-order coupling
term absent from the continuous-time velocity. -/
theorem euler_error_formula
    (rate feedback target : ℝ) (state : ScalarFAState) :
    error target (eulerStep rate feedback target state) =
      error target state -
        rate * error target state *
          (state.hiddenWeight ^ 2 +
            feedback * state.outputWeight) -
        rate ^ 2 * feedback * state.hiddenWeight *
          error target state ^ 2 := by
  simp [error, eulerStep, hiddenVelocity, outputVelocity]
  ring

/-- A small finite step improves the concrete zero-invariant fixture. -/
theorem small_euler_step_improves :
    let state : ScalarFAState := ⟨1, 1 / 2⟩
    loss 1 (eulerStep (1 / 10) 1 1 state) < loss 1 state := by
  norm_num [loss, error, eulerStep, hiddenVelocity, outputVelocity]

/-- Continuous-time nonincrease does not license an arbitrary Euler rate:
the same zero-invariant fixture overshoots at rate ten. -/
theorem large_euler_step_increases :
    let state : ScalarFAState := ⟨1, 1 / 2⟩
    alignmentInvariant 1 state = 0 ∧
      loss 1 state = 1 / 8 ∧
      loss 1 (eulerStep 10 1 1 state) = 512 ∧
      loss 1 state < loss 1 (eulerStep 10 1 1 state) := by
  norm_num [alignmentInvariant, loss, error, eulerStep,
    hiddenVelocity, outputVelocity]

/-- At the all-zero initialization, the source invariant holds and the error
may be nonzero, yet the instantaneous loss derivative and alignment product
both vanish.  Subsequent dynamics, not a one-point derivative, are required
to explain ignition. -/
theorem zero_initialization_has_flat_instantaneous_loss :
    let state : ScalarFAState := ⟨0, 0⟩
    alignmentInvariant 1 state = 0 ∧
      error 1 state = 1 ∧
      lossVelocity 1 1 state = 0 ∧
      alignmentProduct 1 1 state = 0 := by
  norm_num [alignmentInvariant, error, lossVelocity, errorVelocity,
    outputVelocity, hiddenVelocity, alignmentProduct]

/-- Away from the source initialization manifold, fixed feedback can point
strictly against the backprop hidden update. -/
theorem nonzeroInvariant_can_reverse_alignment :
    let state : ScalarFAState := ⟨0, -1⟩
    alignmentInvariant 1 state = -2 ∧
      alignmentProduct 1 1 state = -1 := by
  norm_num [alignmentInvariant, alignmentProduct, error]

#print axioms alignmentInvariant_directionalDerivative_eq_zero
#print axioms lossVelocity_eq_of_zeroInvariant
#print axioms lossVelocity_neg_of_zeroInvariant
#print axioms alignmentProduct_eq_of_zeroInvariant
#print axioms euler_alignmentInvariant_drift
#print axioms euler_error_formula
#print axioms small_euler_step_improves
#print axioms large_euler_step_increases
#print axioms zero_initialization_has_flat_instantaneous_loss
#print axioms nonzeroInvariant_can_reverse_alignment

end FeedbackAlignmentDynamics

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
