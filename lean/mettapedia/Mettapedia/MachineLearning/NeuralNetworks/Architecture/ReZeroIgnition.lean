import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Zero-gated residual ignition

Bachlechner et al., *ReZero is All You Need: Fast Convergence at Large
Depth* (2020), introduce residual layers

`stateNext = state + gate • branch state`

with every trainable scalar `gate` initialized to zero.  Equations (1) and
(4) give the architecture; Equations (5)--(8) analyze a shared-weight scalar
network.  The paper explicitly notes that zero initialization makes the
network the identity, gives unit input-output Jacobian, and initially blocks
the gradients of parameters internal to the residual branch while leaving the
gate gradient available.

This file recovers those exact boundaries and makes them reusable:

* an arbitrary list of zero-gated residual layers is the identity;
* at zero gate, the output is independent of every branch parameter;
* a unit-gate fixture shows that this independence is not vacuous;
* the scalar depth-`L` recurrence has the closed form from Equation (5);
* its input derivative is one at zero gate;
* its branch-weight derivative vanishes at zero gate;
* its gate derivative and first gradient step recover Equation (8).

The results license zero-gated forward ignition, not immediate learning of the
residual branch.  A training profile must expose and monitor gate departure
before it can rely on branch adaptation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace ReZeroIgnition

noncomputable section

/-! ## Arbitrary residual layers -/

structure GatedResidualLayer
    (State : Type*) [AddCommGroup State] [Module ℝ State] where
  gate : ℝ
  branch : State → State

namespace GatedResidualLayer

variable {State : Type*} [AddCommGroup State] [Module ℝ State]

/-- One residual layer with a scalar gate. -/
def apply (layer : GatedResidualLayer State) (state : State) : State :=
  state + layer.gate • layer.branch state

@[simp]
theorem apply_zero_gate
    (branch : State → State) (state : State) :
    apply ⟨0, branch⟩ state = state := by
  simp [apply]

/-- Execute residual layers in their declared order. -/
def run : List (GatedResidualLayer State) → State → State
  | [], state => state
  | layer :: rest, state => run rest (layer.apply state)

@[simp]
theorem run_nil (state : State) :
    run [] state = state := rfl

@[simp]
theorem run_cons
    (layer : GatedResidualLayer State)
    (rest : List (GatedResidualLayer State))
    (state : State) :
    run (layer :: rest) state = run rest (layer.apply state) := rfl

/-- Source Equations (1) and (4): an arbitrarily deep network whose residual
gates are all zero is exactly the identity map. -/
theorem run_eq_self_of_gates_zero
    (layers : List (GatedResidualLayer State)) (state : State)
    (gates_zero : ∀ layer ∈ layers, layer.gate = 0) :
    run layers state = state := by
  induction layers generalizing state with
  | nil =>
      rfl
  | cons layer rest inductionHypothesis =>
      have layer_zero : layer.gate = 0 :=
        gates_zero layer (by simp)
      have rest_zero :
          ∀ later ∈ rest, later.gate = 0 := by
        intro later later_mem
        exact gates_zero later (by simp [later_mem])
      simp [run, apply, layer_zero,
        inductionHypothesis state rest_zero]

/-- At zero gate, changing parameters internal to the residual branch cannot
change the layer output. -/
theorem zero_gate_branch_parameter_invisible
    {Parameter : Type*}
    (branch : Parameter → State → State)
    (first second : Parameter) (state : State) :
    apply ⟨0, branch first⟩ state =
      apply ⟨0, branch second⟩ state := by
  simp [apply]

/-- Negative fixture: branch parameters are observable once the gate is
nonzero. -/
theorem unit_gate_branch_parameter_visible :
    apply (State := ℝ) ⟨1, fun _ => 0⟩ 0 ≠
      apply (State := ℝ) ⟨1, fun _ => 1⟩ 0 := by
  norm_num [apply]

end GatedResidualLayer

/-! ## The shared-weight scalar network from Equations (5)--(8) -/

/-- One layer of the paper's scalar shared-weight toy model. -/
def toyReZeroStep (gate weight state : ℝ) : ℝ :=
  state + gate * weight * state

/-- Execute `depth` shared-weight scalar residual layers. -/
def toyReZeroOutput
    (depth : ℕ) (gate weight input : ℝ) : ℝ :=
  (toyReZeroStep gate weight)^[depth] input

/-- Source Equation (5), derived from the iterative architecture rather than
taken as its definition. -/
theorem toyReZeroOutput_eq_closed
    (depth : ℕ) (gate weight input : ℝ) :
    toyReZeroOutput depth gate weight input =
      (1 + gate * weight) ^ depth * input := by
  induction depth generalizing input with
  | zero =>
      simp [toyReZeroOutput]
  | succ depth inductionHypothesis =>
      rw [toyReZeroOutput, Function.iterate_succ_apply]
      change
        toyReZeroOutput depth gate weight
            (toyReZeroStep gate weight input) = _
      rw [inductionHypothesis]
      simp [toyReZeroStep, pow_succ']
      ring

@[simp]
theorem toyReZeroOutput_zero_gate
    (depth : ℕ) (weight input : ℝ) :
    toyReZeroOutput depth 0 weight input = input := by
  simp [toyReZeroOutput_eq_closed]

/-- The scalar input-output derivative at arbitrary gate and weight. -/
theorem toyReZeroOutput_hasDerivAt_input
    (depth : ℕ) (gate weight input : ℝ) :
    HasDerivAt
      (fun candidate =>
        toyReZeroOutput depth gate weight candidate)
      ((1 + gate * weight) ^ depth)
      input := by
  simp_rw [toyReZeroOutput_eq_closed]
  simpa [mul_comm] using
    (hasDerivAt_id input).mul_const
      ((1 + gate * weight) ^ depth)

/-- Initial scalar dynamical isometry: the input-output derivative is exactly
one at zero gate, independently of depth and branch weight. -/
theorem toyReZeroOutput_zero_gate_hasDerivAt_input
    (depth : ℕ) (weight input : ℝ) :
    HasDerivAt
      (fun candidate =>
        toyReZeroOutput depth 0 weight candidate)
      1 input := by
  simpa using
    toyReZeroOutput_hasDerivAt_input depth 0 weight input

/-- Source Equation (6): the exact branch-weight derivative of the scalar
network output. -/
theorem toyReZeroOutput_hasDerivAt_weight
    (depth : ℕ) (gate weight input : ℝ) :
    HasDerivAt
      (fun candidate =>
        toyReZeroOutput depth gate candidate input)
      ((depth * (1 + gate * weight) ^ (depth - 1) * gate) *
        input)
      weight := by
  simp_rw [toyReZeroOutput_eq_closed]
  simpa using
    ((hasDerivAt_const weight (1 : ℝ)).add
      ((hasDerivAt_const weight gate).mul
        (hasDerivAt_id weight))).pow depth |>.mul_const input

/-- The source's branch-learning boundary: every branch-weight derivative is
zero at initialization, at every depth. -/
theorem toyReZeroOutput_zero_gate_hasDerivAt_weight
    (depth : ℕ) (weight input : ℝ) :
    HasDerivAt
      (fun candidate =>
        toyReZeroOutput depth 0 candidate input)
      0 weight := by
  simpa using
    toyReZeroOutput_hasDerivAt_weight depth 0 weight input

/-- The stronger cost-level boundary: because the zero-gated network output
does not depend on the branch weight, any outer cost has zero branch-weight
derivative, even without differentiability assumptions on that cost. -/
theorem toyReZeroCost_zero_gate_hasDerivAt_weight
    (depth : ℕ) (weight input : ℝ) (cost : ℝ → ℝ) :
    HasDerivAt
      (fun candidate =>
        cost (toyReZeroOutput depth 0 candidate input))
      0 weight := by
  simpa [toyReZeroOutput_eq_closed] using
    hasDerivAt_const weight (cost input)

/-- Exact derivative of the scalar network output with respect to its gate. -/
theorem toyReZeroOutput_hasDerivAt_gate
    (depth : ℕ) (gate weight input : ℝ) :
    HasDerivAt
      (fun candidate =>
        toyReZeroOutput depth candidate weight input)
      ((depth * (1 + gate * weight) ^ (depth - 1) * weight) *
        input)
      gate := by
  simp_rw [toyReZeroOutput_eq_closed]
  simpa [mul_comm] using
    ((hasDerivAt_const gate (1 : ℝ)).add
      ((hasDerivAt_id gate).mul_const weight)).pow depth |>.mul_const input

/-- At zero gate, the gate derivative is the depth-amplified branch signal. -/
theorem toyReZeroOutput_zero_gate_hasDerivAt_gate
    (depth : ℕ) (weight input : ℝ) :
    HasDerivAt
      (fun candidate =>
        toyReZeroOutput depth candidate weight input)
      (depth * weight * input)
      0 := by
  simpa [mul_assoc] using
    toyReZeroOutput_hasDerivAt_gate depth 0 weight input

/-- Source Equation (8), with an arbitrary differentiable outer cost: the
first gate gradient is the output-cost gradient times the depth-amplified
branch signal. -/
theorem toyReZeroCost_zero_gate_hasDerivAt_gate
    (depth : ℕ) (weight input : ℝ)
    (cost : ℝ → ℝ) (costGradient : ℝ)
    (cost_derivative : HasDerivAt cost costGradient input) :
    HasDerivAt
      (fun gate =>
        cost (toyReZeroOutput depth gate weight input))
      (costGradient * (depth * weight * input))
      0 := by
  change HasDerivAt
    (cost ∘ fun gate =>
      toyReZeroOutput depth gate weight input)
    (costGradient * (depth * weight * input)) 0
  have output_derivative :=
    toyReZeroOutput_hasDerivAt_gate depth 0 weight input
  have cost_at_output :
      HasDerivAt cost costGradient
        (toyReZeroOutput depth 0 weight input) := by
    simpa [toyReZeroOutput_eq_closed] using cost_derivative
  have composed := cost_at_output.comp 0 output_derivative
  simpa only [zero_mul, add_zero, one_pow, one_mul, mul_assoc] using
    composed

/-- One scalar gradient-descent step. -/
def scalarGradientStep
    (rate parameter gradient : ℝ) : ℝ :=
  parameter - rate * gradient

/-- The first gate update from zero, recovering the algebraic update in
Equation (8). -/
theorem first_gate_gradientStep_eq_source
    (depth : ℕ) (rate weight input costGradient : ℝ) :
    scalarGradientStep rate 0
        (costGradient * (depth * weight * input)) =
      -rate * depth * weight * input * costGradient := by
  simp [scalarGradientStep]
  ring

/-- Positive fixture: a live branch and nonzero cost derivative move the gate
away from zero on the first update. -/
theorem first_gate_gradientStep_live :
    scalarGradientStep 1 0
        ((1 : ℝ) * ((2 : ℕ) * 3 * 4)) = -24 := by
  norm_num [scalarGradientStep]

/-- Negative fixture: a dead branch weight leaves both the gate and the branch
parameters unable to ignite through this scalar path. -/
theorem zero_branch_first_gate_gradientStep_dead
    (depth : ℕ) (rate input costGradient : ℝ) :
    scalarGradientStep rate 0
        (costGradient * (depth * 0 * input)) = 0 := by
  simp [scalarGradientStep]

#print axioms GatedResidualLayer.run_eq_self_of_gates_zero
#print axioms GatedResidualLayer.zero_gate_branch_parameter_invisible
#print axioms GatedResidualLayer.unit_gate_branch_parameter_visible
#print axioms toyReZeroOutput_eq_closed
#print axioms toyReZeroOutput_zero_gate_hasDerivAt_input
#print axioms toyReZeroCost_zero_gate_hasDerivAt_weight
#print axioms toyReZeroCost_zero_gate_hasDerivAt_gate
#print axioms first_gate_gradientStep_eq_source
#print axioms zero_branch_first_gate_gradientStep_dead

end

end ReZeroIgnition

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
