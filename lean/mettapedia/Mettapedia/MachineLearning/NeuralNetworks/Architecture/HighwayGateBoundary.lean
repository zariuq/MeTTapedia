import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ReZeroIgnition

/-!
# Highway-gate interpolation and Jacobian boundary

Srivastava, Greff, and Schmidhuber, *Training Very Deep Networks* (2015),
define the coupled highway layer

`output = gate • transform + (1 - gate) • input`

in Equations (2)--(3).  This file recovers its exact carry and transform
endpoints, residual form, perturbation size, and pairwise propagation bound.

The source's Equation (5) informally associates a zero transform-gate value
with the identity Jacobian.  For an input-dependent gate, the mathematically
correct derivative contains an additional
`(transform input - input) * gateDerivative` term.  The theorem below states
the exact derivative, gives sufficient identity conditions, and exhibits a
polynomial counterexample where the gate and output equal the carry endpoint
at one point but the derivative is two rather than one.

The standard logistic gate is also proved strictly between zero and one at
every finite input.  Thus a finite negative bias approximates, but never
literally realizes, the exact carry endpoint.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace HighwayGateBoundary

noncomputable section

/-! ## Coupled constant-gate highway layers -/

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- The coupled transform/carry highway interpolation from source Equation
(3), with a scalar gate shared across the state. -/
def highway (gate : ℝ) (transformed input : State) : State :=
  gate • transformed + (1 - gate) • input

@[simp]
theorem highway_zero_gate
    (transformed input : State) :
    highway 0 transformed input = input := by
  simp [highway]

@[simp]
theorem highway_one_gate
    (transformed input : State) :
    highway 1 transformed input = transformed := by
  simp [highway]

/-- The highway layer is a residual layer with residual gate `gate`. -/
theorem highway_eq_residual
    (gate : ℝ) (transformed input : State) :
    highway gate transformed input =
      input + gate • (transformed - input) := by
  simp [highway, smul_sub]
  module

/-- Exact distance from the carry path. -/
theorem norm_highway_sub_input
    (gate : ℝ) (transformed input : State) :
    ‖highway gate transformed input - input‖ =
      |gate| * ‖transformed - input‖ := by
  rw [highway_eq_residual]
  simp [norm_smul, Real.norm_eq_abs]

/-- A gate-magnitude certificate bounds the highway perturbation from carry. -/
theorem norm_highway_sub_input_le
    (gate gateBudget : ℝ) (transformed input : State)
    (gate_bounded : |gate| ≤ gateBudget) :
    ‖highway gate transformed input - input‖ ≤
      gateBudget * ‖transformed - input‖ := by
  rw [norm_highway_sub_input]
  exact mul_le_mul_of_nonneg_right gate_bounded (norm_nonneg _)

/-- Pairwise propagation through a coupled highway layer.  When the transform
has pairwise rate `L` and `gate ∈ [0,1]`, the highway rate is the convex
combination `(1-gate) + gate*L`. -/
theorem norm_highway_sub_highway_le
    (gate transformRate : ℝ)
    (transform : State → State)
    (left right : State)
    (gate_nonnegative : 0 ≤ gate)
    (gate_at_most_one : gate ≤ 1)
    (transform_pair_bound :
      ‖transform left - transform right‖ ≤
        transformRate * ‖left - right‖) :
    ‖highway gate (transform left) left -
        highway gate (transform right) right‖ ≤
      ((1 - gate) + gate * transformRate) * ‖left - right‖ := by
  have carry_nonnegative : 0 ≤ 1 - gate := sub_nonneg.mpr gate_at_most_one
  have expansion :
      highway gate (transform left) left -
          highway gate (transform right) right =
        gate • (transform left - transform right) +
          (1 - gate) • (left - right) := by
    simp [highway, smul_sub]
    module
  rw [expansion]
  calc
    ‖gate • (transform left - transform right) +
        (1 - gate) • (left - right)‖ ≤
      ‖gate • (transform left - transform right)‖ +
        ‖(1 - gate) • (left - right)‖ := norm_add_le _ _
    _ = gate * ‖transform left - transform right‖ +
        (1 - gate) * ‖left - right‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg gate_nonnegative, abs_of_nonneg carry_nonnegative]
    _ ≤ gate * (transformRate * ‖left - right‖) +
        (1 - gate) * ‖left - right‖ := by
      gcongr
    _ = ((1 - gate) + gate * transformRate) *
        ‖left - right‖ := by ring

/-- A nonexpansive transform remains nonexpansive after any coupled gate in
the unit interval. -/
theorem highway_nonexpansive
    (gate transformRate : ℝ)
    (transform : State → State)
    (left right : State)
    (gate_nonnegative : 0 ≤ gate)
    (gate_at_most_one : gate ≤ 1)
    (transformRate_at_most_one : transformRate ≤ 1)
    (transform_pair_bound :
      ‖transform left - transform right‖ ≤
        transformRate * ‖left - right‖) :
    ‖highway gate (transform left) left -
        highway gate (transform right) right‖ ≤
      ‖left - right‖ := by
  have mixed :=
    norm_highway_sub_highway_le
      gate transformRate transform left right
      gate_nonnegative gate_at_most_one transform_pair_bound
  calc
    ‖highway gate (transform left) left -
        highway gate (transform right) right‖ ≤
      ((1 - gate) + gate * transformRate) * ‖left - right‖ := mixed
    _ ≤ 1 * ‖left - right‖ := by
      gcongr
      nlinarith
    _ = ‖left - right‖ := one_mul _

/-! ## Exact scalar Jacobian with an input-dependent gate -/

/-- Scalar input-dependent highway layer. -/
def scalarHighway
    (transform gate : ℝ → ℝ) (input : ℝ) : ℝ :=
  input + (transform input - input) * gate input

/-- The residual definition is exactly the source's coupled transform/carry
equation. -/
theorem scalarHighway_eq_source
    (transform gate : ℝ → ℝ) (input : ℝ) :
    scalarHighway transform gate input =
      transform input * gate input + input * (1 - gate input) := by
  simp [scalarHighway]
  ring

/-- Correct derivative of an input-dependent highway layer. -/
theorem hasDerivAt_scalarHighway
    (transform gate : ℝ → ℝ)
    (input transformDerivative gateDerivative : ℝ)
    (transform_hasDeriv :
      HasDerivAt transform transformDerivative input)
    (gate_hasDeriv :
      HasDerivAt gate gateDerivative input) :
    HasDerivAt
      (scalarHighway transform gate)
      (1 + ((transformDerivative - 1) * gate input +
        (transform input - input) * gateDerivative))
      input := by
  have residualDerivative :
      HasDerivAt
        (fun candidate =>
          (transform candidate - candidate) * gate candidate)
        ((transformDerivative - 1) * gate input +
          (transform input - input) * gateDerivative)
        input :=
    (transform_hasDeriv.sub (hasDerivAt_id input)).mul gate_hasDeriv
  exact (hasDerivAt_id input).add residualDerivative

/-- A pointwise zero gate has identity derivative when the gate is also
locally flat. -/
theorem hasDerivAt_scalarHighway_identity_of_gate_zero_flat
    (transform gate : ℝ → ℝ)
    (input transformDerivative : ℝ)
    (transform_hasDeriv :
      HasDerivAt transform transformDerivative input)
    (gate_hasDeriv : HasDerivAt gate 0 input)
    (gate_zero : gate input = 0) :
    HasDerivAt (scalarHighway transform gate) 1 input := by
  convert hasDerivAt_scalarHighway
    transform gate input transformDerivative 0
    transform_hasDeriv gate_hasDeriv using 1
  simp [gate_zero]

/-- Transform/input agreement is the other sufficient condition that removes
the gate-derivative term at a pointwise zero gate. -/
theorem hasDerivAt_scalarHighway_identity_of_gate_zero_agreement
    (transform gate : ℝ → ℝ)
    (input transformDerivative gateDerivative : ℝ)
    (transform_hasDeriv :
      HasDerivAt transform transformDerivative input)
    (gate_hasDeriv :
      HasDerivAt gate gateDerivative input)
    (gate_zero : gate input = 0)
    (transform_agrees : transform input = input) :
    HasDerivAt (scalarHighway transform gate) 1 input := by
  convert hasDerivAt_scalarHighway
    transform gate input transformDerivative gateDerivative
    transform_hasDeriv gate_hasDeriv using 1
  simp [gate_zero, transform_agrees]

private def counterTransform (_ : ℝ) : ℝ := 1

private def counterGate (input : ℝ) : ℝ := input

private def counterHighway (input : ℝ) : ℝ :=
  scalarHighway counterTransform counterGate input

theorem counter_gate_is_zero :
    counterGate 0 = 0 := by
  rfl

theorem counter_output_equals_carry :
    counterHighway 0 = 0 := by
  norm_num [counterHighway, scalarHighway, counterTransform, counterGate]

theorem counter_highway_has_derivative_two :
    HasDerivAt counterHighway 2 0 := by
  change HasDerivAt
    (scalarHighway (fun _ : ℝ => (1 : ℝ)) (fun input : ℝ => input))
    2 0
  convert
    hasDerivAt_scalarHighway
      (fun _ : ℝ => (1 : ℝ))
      (fun input : ℝ => input)
      0 0 1
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ)))
      (hasDerivAt_id (0 : ℝ)) using 1
  all_goals norm_num

/-- Pointwise gate value zero is not sufficient for the identity Jacobian. -/
theorem pointwise_zero_gate_not_identity_jacobian :
    ¬ HasDerivAt counterHighway 1 0 := by
  intro identityDerivative
  have : (1 : ℝ) = 2 :=
    identityDerivative.unique counter_highway_has_derivative_two
  norm_num at this

/-! ## Finite sigmoid biases approximate but do not attain the endpoint -/

/-- Logistic transform-gate parameterization used by the source. -/
def logisticGate (input : ℝ) : ℝ :=
  1 / (1 + Real.exp (-input))

theorem logisticGate_pos (input : ℝ) :
    0 < logisticGate input := by
  unfold logisticGate
  positivity

theorem logisticGate_lt_one (input : ℝ) :
    logisticGate input < 1 := by
  unfold logisticGate
  have exponentialPositive : 0 < Real.exp (-input) := Real.exp_pos _
  rw [div_lt_one (by positivity : 0 < (1 : ℝ) + Real.exp (-input))]
  linarith

theorem logisticGate_ne_zero (input : ℝ) :
    logisticGate input ≠ 0 :=
  ne_of_gt (logisticGate_pos input)

theorem logisticGate_ne_one (input : ℝ) :
    logisticGate input ≠ 1 :=
  ne_of_lt (logisticGate_lt_one input)

/-! ## Independent carry gates are a separate, amplifying architecture -/

/-- Source Equation (2) before imposing the coupling `carry = 1-transform`. -/
def independentHighway
    (transformGate carryGate : ℝ)
    (transformed input : State) : State :=
  transformGate • transformed + carryGate • input

/-- Without complementary coupling, unit transform and carry gates double a
shared signal rather than interpolating it. -/
theorem independent_unit_gates_double :
    independentHighway 1 1 (1 : ℝ) 1 = 2 := by
  norm_num [independentHighway]

theorem coupled_unit_gate_does_not_double :
    highway 1 (1 : ℝ) 1 = 1 := by
  norm_num [highway]

#print axioms highway_zero_gate
#print axioms highway_eq_residual
#print axioms norm_highway_sub_highway_le
#print axioms highway_nonexpansive
#print axioms hasDerivAt_scalarHighway
#print axioms hasDerivAt_scalarHighway_identity_of_gate_zero_flat
#print axioms pointwise_zero_gate_not_identity_jacobian
#print axioms logisticGate_ne_zero
#print axioms independent_unit_gates_double

end

end HighwayGateBoundary

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
