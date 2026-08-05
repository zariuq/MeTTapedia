import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SafeguardedCompositeBlock

/-!
# Adaptive-restart diagnostics and their exact scope

O'Donoghue and Candès, *Adaptive Restart for Accelerated Gradient Schemes*
(arXiv:1204.3982), propose two inexpensive restart diagnostics:

* restart when the objective value increases;
* restart when the gradient at the previous extrapolated point has positive
  inner product with the latest position displacement.

This file isolates the exact finite logic of those diagnostics.  Function
restart is precisely rejection by the existing zero-tolerance endpoint
safeguard.  A gradient restart implies a function restart under a first-order
lower bound only when the gradient and objective comparison share the same
anchor.  Concrete quadratic fixtures show that the two source diagnostics can
disagree when the gradient is evaluated at a distinct extrapolated point, and
that even a same-anchor function increase need not trigger the gradient test.

The module also records the operational meaning of restart: preserve the
current position while setting the extrapolated position equal to it, thereby
zeroing the momentum displacement.  These finite statements do not claim that
either adaptive diagnostic is a universal convergence certificate outside the
source paper's convex or locally quadratic regimes.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace AdaptiveRestartDiagnostics

open SafeguardedCompositeBlock
open scoped InnerProductSpace

noncomputable section

variable {State : Type*}

/-- The source paper's function-value restart diagnostic. -/
def FunctionRestart
    (objective : State → ℝ) (previous current : State) : Prop :=
  objective previous < objective current

/-- The function-value diagnostic is exactly zero-tolerance endpoint
rejection by the reusable safeguarded-block interface. -/
theorem functionRestart_iff_endpointRejected
    (objective : State → ℝ) (current candidate : State) :
    FunctionRestart objective current candidate ↔
      ¬ EndpointAccepted objective 0 current candidate := by
  simp [FunctionRestart, EndpointAccepted]

/-- A function restart selects the declared baseline step. -/
theorem functionRestart_selects_baseline
    (objective : State → ℝ)
    (baseline accelerated : State → State) (state : State)
    (restart :
      FunctionRestart objective state (accelerated state)) :
    safeguardedBlock objective 0 baseline accelerated state =
      baseline state := by
  apply safeguardedBlock_eq_baseline
  exact (functionRestart_iff_endpointRejected
    objective state (accelerated state)).mp restart

/-- Without a function restart, the complete accelerated proposal is
accepted. -/
theorem noFunctionRestart_selects_accelerated
    (objective : State → ℝ)
    (baseline accelerated : State → State) (state : State)
    (noRestart :
      ¬ FunctionRestart objective state (accelerated state)) :
    safeguardedBlock objective 0 baseline accelerated state =
      accelerated state := by
  apply safeguardedBlock_eq_accelerated
  unfold EndpointAccepted
  simp only [add_zero]
  unfold FunctionRestart at noRestart
  exact le_of_not_gt noRestart

section InnerProduct

variable [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- The source paper's gradient restart diagnostic, with the gradient value
provided at its actual evaluation point. -/
def GradientRestart
    (gradientAtLookahead previous current : State) : Prop :=
  0 < ⟪gradientAtLookahead, current - previous⟫_ℝ

/-- A first-order lower bound at one declared anchor.  For a differentiable
convex objective this is supplied by its gradient at that same anchor. -/
def FirstOrderLowerBoundAt
    (objective : State → ℝ) (gradient anchor : State) : Prop :=
  ∀ candidate,
    objective anchor + ⟪gradient, candidate - anchor⟫_ℝ ≤
      objective candidate

/-- The gradient diagnostic says exactly that the momentum displacement and
negative gradient form an obtuse angle. -/
theorem gradientRestart_iff_negativeGradient_obtuse
    (gradientAtLookahead previous current : State) :
    GradientRestart gradientAtLookahead previous current ↔
      ⟪-gradientAtLookahead, current - previous⟫_ℝ < 0 := by
  simp [GradientRestart]

/-- When the gradient and comparison use the same anchor and a first-order
lower bound is available, the gradient restart condition forces an objective
increase. -/
theorem gradientRestart_implies_functionRestart_of_sameAnchor
    (objective : State → ℝ) (gradient previous current : State)
    (lowerBound : FirstOrderLowerBoundAt objective gradient previous)
    (restart : GradientRestart gradient previous current) :
    FunctionRestart objective previous current := by
  unfold GradientRestart at restart
  unfold FunctionRestart
  have strictLinear :
      objective previous <
        objective previous + ⟪gradient, current - previous⟫_ℝ := by
    linarith
  exact lt_of_lt_of_le strictLinear (lowerBound current)

end InnerProduct

/-- Position and extrapolated position carried by a momentum method. -/
@[ext]
structure MomentumState (State : Type*) where
  position : State
  extrapolated : State

/-- Restart at the current position and erase the extrapolation history. -/
def resetMomentum (state : MomentumState State) : MomentumState State :=
  { position := state.position
    extrapolated := state.position }

@[simp] theorem resetMomentum_position
    (state : MomentumState State) :
    (resetMomentum state).position = state.position := rfl

@[simp] theorem resetMomentum_extrapolated
    (state : MomentumState State) :
    (resetMomentum state).extrapolated = state.position := rfl

/-- Repeating a restart changes nothing further. -/
@[simp] theorem resetMomentum_idempotent
    (state : MomentumState State) :
    resetMomentum (resetMomentum state) = resetMomentum state := by
  rfl

section Momentum

variable [AddCommGroup State]

/-- Displacement contributed by momentum. -/
def momentumDisplacement (state : MomentumState State) : State :=
  state.extrapolated - state.position

/-- Restart zeros the momentum displacement. -/
@[simp] theorem momentumDisplacement_resetMomentum
    (state : MomentumState State) :
    momentumDisplacement (resetMomentum state) = 0 := by
  simp [momentumDisplacement, resetMomentum]

end Momentum

/-! ## Exact scalar-quadratic boundaries -/

def scalarQuadratic (state : ℝ) : ℝ :=
  state ^ 2 / 2

def scalarGradient (state : ℝ) : ℝ :=
  state

/-- The scalar quadratic gradient supplies the required first-order lower
bound at every anchor. -/
theorem scalarQuadratic_firstOrderLowerBoundAt (anchor : ℝ) :
    FirstOrderLowerBoundAt scalarQuadratic (scalarGradient anchor) anchor := by
  intro candidate
  simp only [scalarQuadratic, scalarGradient, RCLike.inner_apply, conj_trivial]
  nlinarith [sq_nonneg (candidate - anchor)]

/-- At a common anchor, the scalar quadratic gradient diagnostic implies the
function diagnostic. -/
theorem scalarQuadratic_gradientRestart_implies_functionRestart
    (previous current : ℝ)
    (restart :
      GradientRestart (scalarGradient previous) previous current) :
    FunctionRestart scalarQuadratic previous current :=
  gradientRestart_implies_functionRestart_of_sameAnchor
    scalarQuadratic (scalarGradient previous) previous current
    (scalarQuadratic_firstOrderLowerBoundAt previous) restart

/-- With a distinct extrapolated point, the gradient diagnostic can trigger
even though the objective strictly improves. -/
theorem lookaheadGradient_can_restart_during_improvement :
    GradientRestart (scalarGradient (-1)) 1 0 ∧
      ¬ FunctionRestart scalarQuadratic 1 0 := by
  norm_num [GradientRestart, FunctionRestart, scalarGradient,
    scalarQuadratic, RCLike.inner_apply]

/-- Even at the same anchor, a finite overshoot can raise the objective while
the local gradient diagnostic does not trigger. -/
theorem functionIncrease_without_sameAnchorGradientRestart :
    FunctionRestart scalarQuadratic 1 (-2) ∧
      ¬ GradientRestart (scalarGradient 1) 1 (-2) := by
  norm_num [GradientRestart, FunctionRestart, scalarGradient,
    scalarQuadratic, RCLike.inner_apply]

/-- Restart preserves the current position while erasing a nonzero momentum
displacement in a concrete state. -/
theorem resetMomentum_example :
    resetMomentum (MomentumState.mk (1 : ℝ) 3) =
      MomentumState.mk 1 1 ∧
    momentumDisplacement
        (resetMomentum (MomentumState.mk (1 : ℝ) 3)) = 0 := by
  norm_num [resetMomentum, momentumDisplacement]

#print axioms gradientRestart_iff_negativeGradient_obtuse
#print axioms gradientRestart_implies_functionRestart_of_sameAnchor
#print axioms functionRestart_iff_endpointRejected
#print axioms functionRestart_selects_baseline
#print axioms noFunctionRestart_selects_accelerated
#print axioms momentumDisplacement_resetMomentum
#print axioms resetMomentum_idempotent
#print axioms scalarQuadratic_firstOrderLowerBoundAt
#print axioms scalarQuadratic_gradientRestart_implies_functionRestart
#print axioms lookaheadGradient_can_restart_during_improvement
#print axioms functionIncrease_without_sameAnchorGradientRestart
#print axioms resetMomentum_example

end

end AdaptiveRestartDiagnostics

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
