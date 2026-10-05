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

/-- An operational trace judgment with a declared list of observations per
step. Empty observations retain their underlying step and transition count. -/
inductive ObservedTrace {Object : Type uObject}
    {Step : Object → Object → Type uStep} {Event : Type uEvent}
    (observe : {source target : Object} → Step source target → List Event) :
    Nat → Object → Object → List Event → Prop where
  | refl (source : Object) : ObservedTrace (Step := Step) (@observe) 0 source source []
  | cons {count : Nat} {source middle target : Object} {observations : List Event}
      (edge : Step source middle)
      (rest : ObservedTrace (Step := Step) (@observe) count middle target observations) :
      ObservedTrace (Step := Step) (@observe) (count + 1) source target (observe edge ++ observations)

namespace ObservedTrace

theorem comp (observe : {source target : Object} → Step source target → List Event)
    {first second : Nat} {source middle target : Object} {leftEvents rightEvents : List Event}
    (left : ObservedTrace (Step := Step) (@observe) first source middle leftEvents)
    (right : ObservedTrace (Step := Step) (@observe) second middle target rightEvents) :
    ObservedTrace (Step := Step) (@observe) (first + second) source target (leftEvents ++ rightEvents) := by
  induction left with
  | refl state => simpa using right
  | cons edge rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using
        ObservedTrace.cons edge (ih right)

/-- Changing the representation of step evidence preserves the declared
observation. The state endpoints and number of steps are unchanged. -/
theorem map {OtherStep : Object → Object → Type*}
    (observe : {source target : Object} → Step source target → List Event)
    (otherObserve : {source target : Object} → OtherStep source target → List Event)
    (mapStep : {source target : Object} → Step source target → OtherStep source target)
    (preserves : ∀ {source target} (edge : Step source target),
      otherObserve (mapStep edge) = observe edge)
    {count : Nat} {source target : Object} {observations : List Event}
    (trace : ObservedTrace (Step := Step) (@observe) count source target observations) :
    ObservedTrace (Step := OtherStep) (@otherObserve) count source target observations := by
  induction trace with
  | refl state => exact .refl state
  | cons edge rest ih => simpa only [preserves] using ObservedTrace.cons (mapStep edge) ih

/-- A reported event comes from one of the real steps of the trace. -/
theorem mem_has_step
    (observe : {source target : Object} → Step source target → List Event)
    {count : Nat} {source target : Object} {observations : List Event}
    (trace : ObservedTrace (Step := Step) (@observe) count source target observations)
    (event : Event) (member : event ∈ observations) :
    ∃ (before after : Object) (edge : Step before after), event ∈ observe edge := by
  induction trace with
  | refl state => simp at member
  | @cons count before middle after observations edge rest ih =>
      rcases List.mem_append.mp member with first | later
      · exact ⟨before, middle, edge, first⟩
      · exact ih later

end ObservedTrace

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

/-- The observation judgment describes exactly the finite routes with the
specified transition count and flattened event record. An empty observation
does not remove its step from the witnessing route. -/
theorem observed_trace_iff_route
    (observe : {source target : Object} → Step source target → List Event)
    {count : Nat} {source target : Object} {observations : List Event} :
    ObservedTrace (Step := Step) (@observe) count source target observations ↔
      ∃ route : Route Step source target,
        route.length = count ∧ (trace (@observe) route).flatten = observations := by
  constructor
  · intro admitted
    induction admitted with
    | refl state => exact ⟨.refl state, rfl, rfl⟩
    | cons edge rest ih =>
        obtain ⟨route, countEq, observationsEq⟩ := ih
        exact ⟨.cons edge route, by simp [length, countEq],
          by simp [trace, observationsEq]⟩
  · rintro ⟨route, rfl, rfl⟩
    induction route with
    | refl state => exact .refl state
    | cons edge rest ih =>
        simpa only [trace, length, List.flatten_cons] using ObservedTrace.cons edge ih

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
