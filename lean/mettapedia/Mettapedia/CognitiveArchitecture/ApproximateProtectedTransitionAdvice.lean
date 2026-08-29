import Mettapedia.CognitiveArchitecture.ProtectedMindAgentWave
import Mettapedia.Cybernetics.ApproximateGeometricVisibility

/-!
# Approximate geometric advice versus exact protected-transition authority

Geometric reconstruction with positive error can guide a cognitive process,
but it does not satisfy an exact protected-transition readout.  Zero error in
a point-separating geometry is the principled upgrade boundary: only there can
the approximate readout construct the exact transition constraint.

This keeps useful learned or geometric advice available without silently
discarding its uncertainty when it enters an execution-authority interface.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ApproximateProtectedTransitionAdvice

noncomputable section

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.ApproximateGeometricVisibility
open Mettapedia.Cybernetics.GeometricGoalCostControl
open Mettapedia.CognitiveArchitecture.Agent.WellbeingObserverTransformationBoundary
open Mettapedia.CognitiveArchitecture.ProtectedMindAgentWave
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

universe uState uView uValue

/-! ## Exact compatibility of the two readout boundaries -/

/-- The appraisal and geometric-value interfaces use the same exact
factorization law.  Their different names record different downstream roles,
not different mathematics. -/
theorem appraisalVisibleAt_iff_valueVisibleAt
    {State : Type uState} {View : Type uView} {Value : Type uValue}
    (value : State -> Value) (observer : Observer State View) :
    AppraisalVisibleAt value observer <-> ValueVisibleAt value observer :=
  Iff.rfl

/-- A zero-error geometric readout in a separating geometry constructs an
exact protected-transition constraint for any independently authored
transition relation. -/
def TransitionConstraint.ofZeroError
    {State : Type uState} {View : Type uView} {Value : Type uValue}
    {geometry : ValueGeometry Value} {value : State -> Value}
    {observer : Observer State View}
    (readout : ApproximateValueReadout geometry value observer 0)
    (separates : SeparatesPoints geometry)
    (Allows : Value -> Value -> Prop) :
    TransitionConstraint observer.observe where
  Appraisal := Value
  appraisal := value
  readout := Classical.choose (readout.toExactOfZero separates)
  agrees := Classical.choose_spec (readout.toExactOfZero separates)
  Allows := Allows

/-- The promoted constraint exposes exactly the original authored value, not
the approximate reconstruction as a replacement semantics. -/
theorem ofZeroError_visible
    {State : Type uState} {View : Type uView} {Value : Type uValue}
    {geometry : ValueGeometry Value} {value : State -> Value}
    {observer : Observer State View}
    (readout : ApproximateValueReadout geometry value observer 0)
    (separates : SeparatesPoints geometry)
    (Allows : Value -> Value -> Prop) :
    AppraisalVisibleAt value observer :=
  (TransitionConstraint.ofZeroError readout separates Allows).visible

/-! ## A positive-error reconstruction is strictly advisory -/

namespace Canary

open Mettapedia.Cybernetics.ApproximateGeometricVisibility.Canary

/-- The coarse Boolean view cannot exactly recover the hidden real-valued
coordinate. -/
theorem hiddenValue_not_exactly_visible :
    Not (AppraisalVisibleAt hiddenValue coarseObserver) := by
  rintro ⟨readout, agrees⟩
  have seesZero := agrees (false, false)
  have seesOne := agrees (false, true)
  norm_num [hiddenValue, coarseObserver] at seesZero seesOne
  linarith

/-- Decisive boundary: radius-one-half guidance exists on the coarse view,
while exact protected-transition visibility at that same view does not. -/
theorem positive_error_advice_does_not_grant_exact_authority :
    ApproximatelyVisibleAt realGeometry hiddenValue coarseObserver (1 / 2) /\
      Not (AppraisalVisibleAt hiddenValue coarseObserver) :=
  ⟨half_visible, hiddenValue_not_exactly_visible⟩

/-- At the exact observer, the zero-error readout crosses the boundary and
constructs an exact constraint. -/
def exactConstraint : TransitionConstraint exactObserver.observe :=
  TransitionConstraint.ofZeroError exactZeroReadout realGeometry_separates
    (fun before after : ℝ => before <= after)

theorem zero_error_advice_grants_exact_visibility :
    AppraisalVisibleAt hiddenValue exactObserver :=
  exactConstraint.visible

/-- Point separation prevents a zero-error readout from being hidden inside
the same coarse observer that only supported positive-error advice. -/
theorem coarse_zero_error_refused :
    Not (ApproximatelyVisibleAt realGeometry hiddenValue coarseObserver 0) := by
  rintro ⟨readout⟩
  exact hiddenValue_not_exactly_visible
    (ofZeroError_visible readout realGeometry_separates
      (fun before after : ℝ => before <= after))

end Canary

#print axioms appraisalVisibleAt_iff_valueVisibleAt
#print axioms TransitionConstraint.ofZeroError
#print axioms ofZeroError_visible
#print axioms Canary.positive_error_advice_does_not_grant_exact_authority
#print axioms Canary.zero_error_advice_grants_exact_visibility
#print axioms Canary.coarse_zero_error_refused

end


end Mettapedia.CognitiveArchitecture.ApproximateProtectedTransitionAdvice
