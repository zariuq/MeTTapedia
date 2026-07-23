import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.ContinuousHolomorphic
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ImplicitEquilibrium

/-!
# Implicit holomorphic equilibrium branches

This module lifts the continuous contour result from a solved scalar formula
to nonlinear residual equations on complex Banach spaces.  A strict derivative
and an invertible state Jacobian construct a locally unique equilibrium branch;
the branch derivative is obtained from the implicit-function theorem rather
than assumed.  Disk-wide regularity remains an explicit additional premise for
a finite-radius contour readout.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances

open Complex Metric Filter Topology
open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

universe uState uResponse

variable {State : Type uState} [NormedAddCommGroup State]
  [NormedSpace ℂ State] [CompleteSpace State]
variable {Response : Type uResponse} [NormedAddCommGroup Response]
  [NormedSpace ℂ Response] [CompleteSpace Response]

/-- Complex specialization of the field-generic implicit-equilibrium data. -/
abbrev HolomorphicImplicitEquilibriumAt (State : Type uState)
    [NormedAddCommGroup State] [NormedSpace ℂ State] [CompleteSpace State] :=
  ImplicitEquilibriumAt ℂ State

namespace HolomorphicImplicitEquilibriumAt

variable (problem : HolomorphicImplicitEquilibriumAt State)

/-- Partial derivative of the residual in the complex nudge coordinate. -/
noncomputable def nudgeJacobian : ℂ →L[ℂ] State :=
  ImplicitEquilibriumAt.parameterJacobian problem

/-- Partial derivative of the residual in the state coordinate. -/
noncomputable def stateJacobian : State →L[ℂ] State :=
  ImplicitEquilibriumAt.stateJacobian problem

/-- The locally defined equilibrium branch supplied by the implicit-function
theorem. -/
noncomputable def branch : ℂ → State :=
  ImplicitEquilibriumAt.branch problem

/-- The implicit sensitivity `-J_state⁻¹ J_nudge`. -/
noncomputable def sensitivity : ℂ →L[ℂ] State :=
  ImplicitEquilibriumAt.sensitivity problem

/-- The constructed branch passes through the declared free equilibrium. -/
theorem branch_zero : problem.branch 0 = problem.state0 := by
  exact ImplicitEquilibriumAt.branch_zero problem

/-- Near zero, the constructed branch actually solves the residual equation. -/
theorem eventually_residual_branch_eq_zero :
    ∀ᶠ beta in 𝓝 (0 : ℂ), problem.residual (beta, problem.branch beta) = 0 := by
  exact ImplicitEquilibriumAt.eventually_residual_branch_eq_zero problem

/-- Near the free point, every zero of the residual is exactly the constructed
branch.  This is local uniqueness, not a global equilibrium claim. -/
theorem eventually_residual_eq_zero_iff_branch_eq :
    ∀ᶠ point in 𝓝 ((0 : ℂ), problem.state0),
      problem.residual point = 0 ↔ problem.branch point.1 = point.2 := by
  exact ImplicitEquilibriumAt.eventually_residual_eq_zero_iff_branch_eq problem

/-- The equilibrium derivative is the implicit sensitivity. -/
theorem branch_hasStrictFDerivAt :
    HasStrictFDerivAt problem.branch problem.sensitivity 0 := by
  exact ImplicitEquilibriumAt.branch_hasStrictFDerivAt problem

/-- A declared linear readout converts implicit state sensitivity into the
credit quantity to be extracted. -/
noncomputable def readoutCredit (readout : State →L[ℂ] Response) : Response :=
  readout (problem.sensitivity 1)

/-- Response along the constructed equilibrium branch. -/
noncomputable def response (readout : State →L[ℂ] Response) : ℂ → Response :=
  readout ∘ problem.branch

omit [CompleteSpace Response] in
/-- Differentiating the branch and then the linear readout yields exactly the
declared implicit credit. -/
theorem response_hasDerivAt (readout : State →L[ℂ] Response) :
    HasDerivAt (problem.response readout) (problem.readoutCredit readout) 0 := by
  have composed := readout.hasFDerivAt.comp 0 problem.branch_hasStrictFDerivAt.hasFDerivAt
  change HasDerivAt (readout ∘ problem.branch)
    (readout (problem.sensitivity 1)) 0
  simpa only [ContinuousLinearMap.comp_apply] using composed.hasDerivAt

/-- Under an explicit disk-wide admissibility certificate, the continuous
contour readout equals the nonlinear implicit-equilibrium credit.  The local
implicit-function theorem alone does not supply this global disk premise. -/
theorem continuousReadout_response_eq_readoutCredit
    (readout : State →L[ℂ] Response) {radius : ℝ}
    (radiusPositive : 0 < radius)
    (regular : DiffContOnCl ℂ (problem.response readout) (ball 0 radius)) :
    continuousFirstPhaseReadout (problem.response readout) radius =
      problem.readoutCredit readout := by
  rw [continuousFirstPhaseReadout_eq_deriv _ _ radiusPositive regular]
  exact (problem.response_hasDerivAt readout).deriv

end HolomorphicImplicitEquilibriumAt

/-! ## Singular boundary -/

/-- Negative boundary: a zero state Jacobian is not invertible over `ℂ`, so
the branch construction cannot be licensed from this premise. -/
theorem zero_stateJacobian_not_invertible :
    ¬ (0 : ℂ →L[ℂ] ℂ).IsInvertible := by
  exact zero_stateJacobian_not_invertible_generic

#print axioms HolomorphicImplicitEquilibriumAt.branch_zero
#print axioms HolomorphicImplicitEquilibriumAt.eventually_residual_branch_eq_zero
#print axioms HolomorphicImplicitEquilibriumAt.eventually_residual_eq_zero_iff_branch_eq
#print axioms HolomorphicImplicitEquilibriumAt.branch_hasStrictFDerivAt
#print axioms HolomorphicImplicitEquilibriumAt.response_hasDerivAt
#print axioms HolomorphicImplicitEquilibriumAt.continuousReadout_response_eq_readoutCredit
#print axioms zero_stateJacobian_not_invertible

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances
