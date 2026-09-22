import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# Event traces of proof-relevant routes

A trace retains one event per step. It determines an entire finite route,
including the final state, when the initial state and event determine each
outgoing step. The hypothesis concerns the actual dependent step object,
so it cannot silently identify different witnesses carrying the same event.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Ultrainfinite.Route

universe uObject uStep uEvent

variable {Object : Type uObject} {Step : Object → Object → Type uStep}
variable {Event : Type uEvent}

/-- The ordered event record of a finite route. -/
def trace (event : {source target : Object} → Step source target → Event)
    {source target : Object} : Route Step source target → List Event
  | .refl _ => []
  | .cons step rest => event step :: trace event rest

/-- Transport of endpoints does not change the event record. -/
theorem trace_heq
    (event : {source target : Object} → Step source target → Event)
    {source target otherSource otherTarget : Object}
    {first : Route Step source target}
    {second : Route Step otherSource otherTarget}
    (sameSource : source = otherSource) (sameTarget : target = otherTarget)
    (sameRoute : HEq first second) :
    trace event first = trace event second := by
  cases sameSource
  cases sameTarget
  cases sameRoute
  rfl

@[simp] theorem trace_append
    (event : {source target : Object} → Step source target → Event)
    {source middle target : Object}
    (first : Route Step source middle) (second : Route Step middle target) :
    trace event (first.append second) =
      trace event first ++ trace event second := by
  induction first with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [trace, append, inductionHypothesis]

@[simp] theorem trace_length
    (event : {source target : Object} → Step source target → Event)
    {source target : Object} (route : Route Step source target) :
    (trace event route).length = route.length := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [trace, length, inductionHypothesis]

/-- If each event identifies an outgoing step at its source, a whole event
trace identifies the route and its final state. -/
theorem trace_receipt_injective
    (event : {source target : Object} → Step source target → Event)
    (stepIdentified : ∀ source,
      Function.Injective
        (fun receipt : Σ target, Step source target => event receipt.2))
    (source : Object) :
    Function.Injective
      (fun receipt : Σ target, Route Step source target =>
        trace event receipt.2) := by
  rintro ⟨target, first⟩ ⟨otherTarget, second⟩ equal
  induction first generalizing otherTarget with
  | refl source =>
      cases second with
      | refl => rfl
      | cons step rest => simp [trace] at equal
  | @cons source middle target step rest inductionHypothesis =>
      cases second with
      | refl => simp [trace] at equal
      | @cons _ otherMiddle _ otherStep otherRest =>
          have parts := List.cons.inj equal
          have sameStep :
              (⟨middle, step⟩ : Σ next, Step source next) =
                ⟨otherMiddle, otherStep⟩ :=
            stepIdentified source parts.1
          cases sameStep
          have sameRest := inductionHypothesis otherTarget otherRest parts.2
          cases sameRest
          rfl

end Mettapedia.GSLT.Ultrainfinite.Route

#print axioms Mettapedia.GSLT.Ultrainfinite.Route.trace_receipt_injective
