import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-!
# Field-generic implicit equilibrium branches

This module isolates the implicit-function argument shared by real
primal--dual continuation and complex holomorphic readout.  A residual,
its strict derivative at a declared base equilibrium, and invertibility of
the state Jacobian determine a locally unique branch.  The branch derivative
is the inverse-Jacobian sensitivity; it is not included as independent data.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

open Filter Topology

universe uScalar uState

variable {𝕜 : Type uScalar} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {State : Type uState} [NormedAddCommGroup State]
  [NormedSpace 𝕜 State] [CompleteSpace State]

/-- Local data for an equilibrium equation `residual (parameter, state) = 0`
at `(0, state0)`.  The equilibrium branch and its sensitivity are derived
below rather than supplied by the structure. -/
structure ImplicitEquilibriumAt (𝕜 : Type uScalar) (State : Type uState)
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup State] [NormedSpace 𝕜 State] [CompleteSpace State] where
  residual : 𝕜 × State → State
  state0 : State
  derivative : (𝕜 × State) →L[𝕜] State
  hasStrictDerivative :
    HasStrictFDerivAt residual derivative (0, state0)
  stateJacobianInvertible :
    (derivative ∘L ContinuousLinearMap.inr 𝕜 𝕜 State).IsInvertible
  residualAtFree : residual (0, state0) = 0

namespace ImplicitEquilibriumAt

variable (problem : ImplicitEquilibriumAt 𝕜 State)

/-- Partial derivative of the residual in the continuation parameter. -/
noncomputable def parameterJacobian : 𝕜 →L[𝕜] State :=
  problem.derivative ∘L ContinuousLinearMap.inl 𝕜 𝕜 State

/-- Partial derivative of the residual in the equilibrium state. -/
noncomputable def stateJacobian : State →L[𝕜] State :=
  problem.derivative ∘L ContinuousLinearMap.inr 𝕜 𝕜 State

/-- The locally defined equilibrium branch supplied by the implicit-function
theorem. -/
noncomputable def branch : 𝕜 → State :=
  problem.hasStrictDerivative.implicitFunctionOfProdDomain
    problem.stateJacobianInvertible

/-- The implicit sensitivity `-J_state⁻¹ J_parameter`. -/
noncomputable def sensitivity : 𝕜 →L[𝕜] State :=
  -(problem.stateJacobian).inverse ∘L problem.parameterJacobian

/-- The constructed branch passes through the declared base equilibrium. -/
theorem branch_zero : problem.branch 0 = problem.state0 := by
  exact
    (problem.hasStrictDerivative
      |>.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        problem.stateJacobianInvertible
      |>.self_of_nhds).mp rfl

/-- Near zero, the constructed branch solves the residual equation. -/
theorem eventually_residual_branch_eq_zero :
    ∀ᶠ parameter in 𝓝 (0 : 𝕜),
      problem.residual (parameter, problem.branch parameter) = 0 := by
  filter_upwards
    [problem.hasStrictDerivative.eventually_apply_implicitFunctionOfProdDomain
      problem.stateJacobianInvertible] with parameter residualEqual
  simpa only [branch, problem.residualAtFree] using residualEqual

/-- Near the base point, every zero of the residual is exactly the constructed
branch.  This is local uniqueness, not a global equilibrium claim. -/
theorem eventually_residual_eq_zero_iff_branch_eq :
    ∀ᶠ point in 𝓝 ((0 : 𝕜), problem.state0),
      problem.residual point = 0 ↔ problem.branch point.1 = point.2 := by
  filter_upwards
    [problem.hasStrictDerivative
      |>.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        problem.stateJacobianInvertible] with point equivalence
  simpa only [branch, problem.residualAtFree] using equivalence

/-- The branch derivative is exactly the inverse-Jacobian sensitivity. -/
theorem branch_hasStrictFDerivAt :
    HasStrictFDerivAt problem.branch problem.sensitivity 0 := by
  exact problem.hasStrictDerivative.hasStrictFDerivAt_implicitFunctionOfProdDomain
    problem.stateJacobianInvertible

/-- Conditioning of the state Jacobian controls the response to a declared
parameter forcing direction. -/
theorem norm_sensitivity_apply_le (direction : 𝕜) :
    ‖problem.sensitivity direction‖ ≤
      ‖(problem.stateJacobian).inverse‖ *
        ‖problem.parameterJacobian direction‖ := by
  simpa [sensitivity, ContinuousLinearMap.comp_apply] using
    (problem.stateJacobian.inverse.le_opNorm
      (problem.parameterJacobian direction))

/-- Operator norms give a direction-independent sensitivity certificate. -/
theorem norm_sensitivity_apply_le_opNorm (direction : 𝕜) :
    ‖problem.sensitivity direction‖ ≤
      ‖(problem.stateJacobian).inverse‖ *
        (‖problem.parameterJacobian‖ * ‖direction‖) := by
  calc
    ‖problem.sensitivity direction‖ ≤
        ‖(problem.stateJacobian).inverse‖ *
          ‖problem.parameterJacobian direction‖ :=
      problem.norm_sensitivity_apply_le direction
    _ ≤ ‖(problem.stateJacobian).inverse‖ *
          (‖problem.parameterJacobian‖ * ‖direction‖) := by
      gcongr
      exact problem.parameterJacobian.le_opNorm direction

end ImplicitEquilibriumAt

/-! ## Singular boundary -/

omit [CompleteSpace 𝕜] in
/-- Negative boundary: a zero state Jacobian cannot license an implicit
equilibrium branch over any nontrivial normed field. -/
theorem zero_stateJacobian_not_invertible_generic :
    ¬ (0 : 𝕜 →L[𝕜] 𝕜).IsInvertible := by
  rw [ContinuousLinearMap.isInvertible_zero_iff]
  exact fun impossible => not_subsingleton 𝕜 impossible.1

#print axioms ImplicitEquilibriumAt.branch_zero
#print axioms ImplicitEquilibriumAt.eventually_residual_branch_eq_zero
#print axioms ImplicitEquilibriumAt.eventually_residual_eq_zero_iff_branch_eq
#print axioms ImplicitEquilibriumAt.branch_hasStrictFDerivAt
#print axioms ImplicitEquilibriumAt.norm_sensitivity_apply_le
#print axioms ImplicitEquilibriumAt.norm_sensitivity_apply_le_opNorm
#print axioms zero_stateJacobian_not_invertible_generic

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
