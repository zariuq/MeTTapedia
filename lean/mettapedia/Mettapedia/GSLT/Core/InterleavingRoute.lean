import Mettapedia.GSLT.Core.RouteTrace
import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.GSLT.Core.GSLTConstructions

/-!
# Proof-relevant routes of independent systems

One component moves while the other state is held literally fixed. Projection
retains each component's exact steps but forgets their relative schedule.
Executing two nonempty component routes in the two sequential orders gives
distinct combined routes with the same component projections.

These steps erase soundly into the existing equation-modulo interleaving
product. No converse is claimed for arbitrary component equations: that
product also permits the held state to change to an equivalent representative.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Ultrainfinite.Interleaving

universe uLeft uRight vLeft vRight

variable {Left : Type uLeft} {Right : Type uRight}
variable (LeftStep : Left → Left → Type vLeft)
variable (RightStep : Right → Right → Type vRight)

/-- Real component independence: stepping one side leaves the other state
unchanged. The chosen component and its complete step witness are retained. -/
inductive Step : Left × Right → Left × Right → Type _ where
  | left {source target : Left} (step : LeftStep source target) (partner : Right) :
      Step (source, partner) (target, partner)
  | right {source target : Right} (partner : Left) (step : RightStep source target) :
      Step (partner, source) (partner, target)

variable {LeftStep RightStep}

private def stepLeft {source target : Left × Right} :
    Step LeftStep RightStep source target → Route LeftStep source.1 target.1
  | .left step _ => .cons step (.refl _)
  | .right partner _ => .refl partner

private def stepRight {source target : Left × Right} :
    Step LeftStep RightStep source target → Route RightStep source.2 target.2
  | .left _ partner => .refl partner
  | .right _ step => .cons step (.refl _)

/-- Forget the scheduling of the right component, retaining all left steps. -/
def projectLeft {source target : Left × Right} :
    Route (Step LeftStep RightStep) source target →
      Route LeftStep source.1 target.1
  | .refl _ => .refl _
  | .cons step rest => (stepLeft step).append (projectLeft rest)

/-- Forget the scheduling of the left component, retaining all right steps. -/
def projectRight {source target : Left × Right} :
    Route (Step LeftStep RightStep) source target →
      Route RightStep source.2 target.2
  | .refl _ => .refl _
  | .cons step rest => (stepRight step).append (projectRight rest)

/-- Run the left component while holding the right one fixed. -/
def liftLeft {source target : Left} (route : Route LeftStep source target)
    (partner : Right) :
    Route (Step LeftStep RightStep) (source, partner) (target, partner) :=
  match route with
  | .refl _ => .refl _
  | .cons step rest => .cons (.left step partner) (liftLeft rest partner)

/-- Run the right component while holding the left one fixed. -/
def liftRight (partner : Left) {source target : Right}
    (route : Route RightStep source target) :
    Route (Step LeftStep RightStep) (partner, source) (partner, target) :=
  match route with
  | .refl _ => .refl _
  | .cons step rest => .cons (.right partner step) (liftRight partner rest)

@[simp] theorem projectLeft_append {source middle target : Left × Right}
    (first : Route (Step LeftStep RightStep) source middle)
    (second : Route (Step LeftStep RightStep) middle target) :
    projectLeft (first.append second) =
      (projectLeft first).append (projectLeft second) := by
  induction first with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      cases step <;> simp [Route.append, projectLeft, stepLeft, inductionHypothesis]

@[simp] theorem projectRight_append {source middle target : Left × Right}
    (first : Route (Step LeftStep RightStep) source middle)
    (second : Route (Step LeftStep RightStep) middle target) :
    projectRight (first.append second) =
      (projectRight first).append (projectRight second) := by
  induction first with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      cases step <;> simp [Route.append, projectRight, stepRight, inductionHypothesis]

@[simp] theorem projectLeft_liftLeft {source target : Left}
    (route : Route LeftStep source target) (partner : Right) :
    projectLeft (RightStep := RightStep) (liftLeft route partner) = route := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [liftLeft, projectLeft, stepLeft, Route.append, inductionHypothesis]

@[simp] theorem projectRight_liftLeft {source target : Left}
    (route : Route LeftStep source target) (partner : Right) :
    projectRight (RightStep := RightStep) (liftLeft route partner) =
      .refl partner := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis

@[simp] theorem projectLeft_liftRight (partner : Left) {source target : Right}
    (route : Route RightStep source target) :
    projectLeft (LeftStep := LeftStep) (liftRight partner route) =
      .refl partner := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis => exact inductionHypothesis

@[simp] theorem projectRight_liftRight (partner : Left) {source target : Right}
    (route : Route RightStep source target) :
    projectRight (LeftStep := LeftStep) (liftRight partner route) = route := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [liftRight, projectRight, stepRight, Route.append, inductionHypothesis]

/-- One schedule completes the left route before running the right route. -/
def leftThenRight {leftSource leftTarget : Left} {rightSource rightTarget : Right}
    (left : Route LeftStep leftSource leftTarget)
    (right : Route RightStep rightSource rightTarget) :
    Route (Step LeftStep RightStep) (leftSource, rightSource)
      (leftTarget, rightTarget) :=
  (liftLeft left rightSource).append (liftRight leftTarget right)

/-- The other schedule runs the same components in the opposite order. -/
def rightThenLeft {leftSource leftTarget : Left} {rightSource rightTarget : Right}
    (left : Route LeftStep leftSource leftTarget)
    (right : Route RightStep rightSource rightTarget) :
    Route (Step LeftStep RightStep) (leftSource, rightSource)
      (leftTarget, rightTarget) :=
  (liftRight leftSource right).append (liftLeft left rightTarget)

/-- Either sequential schedule retains exactly the given component routes. -/
theorem schedules_project {leftSource leftTarget : Left}
    {rightSource rightTarget : Right}
    (left : Route LeftStep leftSource leftTarget)
    (right : Route RightStep rightSource rightTarget) :
    projectLeft (leftThenRight left right) = left ∧
      projectRight (leftThenRight left right) = right ∧
      projectLeft (rightThenLeft left right) = left ∧
      projectRight (rightThenLeft left right) = right := by
  simp [leftThenRight, rightThenLeft]

/-- The scheduling event says which genuinely independent component moved. -/
def side {source target : Left × Right} :
    Step LeftStep RightStep source target → Bool
  | .left _ _ => false
  | .right _ _ => true

/-- The two schedules have distinct component-choice traces whenever both
component routes take a step. -/
theorem schedule_traces_distinct {leftSource leftTarget : Left}
    {rightSource rightTarget : Right}
    (left : Route LeftStep leftSource leftTarget)
    (right : Route RightStep rightSource rightTarget)
    (leftNonempty : left.length ≠ 0) (rightNonempty : right.length ≠ 0) :
    Route.trace side (leftThenRight left right) ≠
      Route.trace side (rightThenLeft left right) := by
  cases left with
  | refl => exact False.elim (leftNonempty rfl)
  | cons leftStep leftRest =>
      cases right with
      | refl => exact False.elim (rightNonempty rfl)
      | cons rightStep rightRest =>
          intro traces
          simp [leftThenRight, rightThenLeft, liftLeft, liftRight,
            Route.trace, Route.append, side] at traces

/-- Both schedules are distinct whenever both component routes take a step.
Equality of their component proofs cannot recover this scheduling choice. -/
theorem schedules_distinct {leftSource leftTarget : Left}
    {rightSource rightTarget : Right}
    (left : Route LeftStep leftSource leftTarget)
    (right : Route RightStep rightSource rightTarget)
    (leftNonempty : left.length ≠ 0) (rightNonempty : right.length ≠ 0) :
    leftThenRight left right ≠ rightThenLeft left right := by
  intro equal
  exact schedule_traces_distinct left right leftNonempty rightNonempty
    (congrArg (Route.trace side) equal)

/-- Projection preserves every step once, but not its position relative to
steps from the other component. -/
theorem length_projections {source target : Left × Right}
    (route : Route (Step LeftStep RightStep) source target) :
    route.length = (projectLeft route).length + (projectRight route).length := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      cases step <;> simp [Route.length, projectLeft, projectRight,
        stepLeft, stepRight, Route.append,
        inductionHypothesis, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The strict-held-partner event has the existing interleaving GSLT meaning.
This is sound erasure, not a second authority for product semantics. -/
theorem eraseStep
    (left right : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT)
    {source target : left.theory.Term × right.theory.Term}
    (step : Step left.steps.Evidence right.steps.Evidence source target) :
    (Mettapedia.GSLT.GSLT.interleavingProduct left.theory right.theory).Step
      source target := by
  cases step with
  | left step partner =>
      exact Mettapedia.GSLT.GSLT.interleavingProduct_step_left
        (left.steps.erase step) partner
  | right partner step =>
      exact Mettapedia.GSLT.GSLT.interleavingProduct_step_right
        (right.steps.erase step) partner

end Mettapedia.GSLT.Ultrainfinite.Interleaving

#print axioms Mettapedia.GSLT.Ultrainfinite.Interleaving.schedules_project
#print axioms Mettapedia.GSLT.Ultrainfinite.Interleaving.schedules_distinct
#print axioms Mettapedia.GSLT.Ultrainfinite.Interleaving.eraseStep
