import Mettapedia.GSLT.Dynamics.CompositeObservationDiscipline

/-!
# One-pass realization of composite observation disciplines

`ObservationDiscipline.parallelComposite` is an extensional specification: it
projects a joint history and then runs both collectors.  An implementation
should not allocate the projected histories or traverse the input twice.

This module gives the corresponding streaming interface.  A collector carries
an internal state, an optional transition for each event, and a final readout.
The product construction dispatches each sum event to exactly one component
while retaining the other component's state.  The main theorem proves that
this single-pass product implements the extensional projection-and-product
collector exactly, including partial failure.
-/

namespace Mettapedia.GSLT.Dynamics

universe uEvent uContainer uState uLeftEvent uRightEvent
  uLeftContainer uRightContainer uLeftState uRightState

/-- A collector presented as a state machine.  Failure remains explicit in
the transition, so this covers total streaming folds and partial admission
collectors. -/
structure StreamingWitnessCollector
    (Event : Type uEvent) where
  Container : Type uContainer
  State : Type uState
  initial : State
  step : State -> Event -> Option State
  finish : State -> Container

namespace StreamingWitnessCollector

/-- Run a streaming collector from an explicit internal state. -/
def advance {Event : Type uEvent}
    (collector : StreamingWitnessCollector.{uEvent, uContainer, uState} Event) :
    collector.State -> List Event -> Option collector.State
  | state, [] => some state
  | state, event :: events =>
      (collector.step state event).bind fun next =>
        collector.advance next events

/-- Run from the collector's declared initial state. -/
def run {Event : Type uEvent}
    (collector : StreamingWitnessCollector.{uEvent, uContainer, uState} Event)
    (events : List Event) : Option collector.State :=
  collector.advance collector.initial events

/-- Forget the state-machine presentation and retain its extensional witness
collector. -/
def toCollector {Event : Type uEvent}
    (collector : StreamingWitnessCollector.{uEvent, uContainer, uState} Event) :
    WitnessCollector Event where
  Container := collector.Container
  collect := fun events => (collector.run events).map collector.finish

/-- Streaming across an append is state threading. -/
theorem advance_append {Event : Type uEvent}
    (collector : StreamingWitnessCollector.{uEvent, uContainer, uState} Event)
    (state : collector.State) (first second : List Event) :
    collector.advance state (first ++ second) =
      (collector.advance state first).bind fun middle =>
        collector.advance middle second := by
  induction first generalizing state with
  | nil => rfl
  | cons event events inductionHypothesis =>
      simp only [List.cons_append, advance]
      cases stepEquation : collector.step state event with
      | none => rfl
      | some next =>
          simp only [Option.bind_some]
          exact inductionHypothesis next

/-- A one-pass product collector.  Each event advances exactly its owning
component; the other component state is retained unchanged. -/
def parallelComposite
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left : StreamingWitnessCollector.{uLeftEvent, uLeftContainer, uLeftState}
      LeftEvent)
    (right : StreamingWitnessCollector.{uRightEvent, uRightContainer, uRightState}
      RightEvent) :
    StreamingWitnessCollector (Sum LeftEvent RightEvent) where
  Container := left.Container × right.Container
  State := left.State × right.State
  initial := (left.initial, right.initial)
  step := fun states event =>
    match event with
    | .inl leftEvent =>
        (left.step states.1 leftEvent).map fun nextLeft =>
          (nextLeft, states.2)
    | .inr rightEvent =>
        (right.step states.2 rightEvent).map fun nextRight =>
          (states.1, nextRight)
  finish := fun states => (left.finish states.1, right.finish states.2)

/-- The one-pass state is exactly the pair obtained by running the two
projected histories separately. -/
theorem parallelComposite_advance
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left : StreamingWitnessCollector.{uLeftEvent, uLeftContainer, uLeftState}
      LeftEvent)
    (right : StreamingWitnessCollector.{uRightEvent, uRightContainer, uRightState}
      RightEvent)
    (leftState : left.State) (rightState : right.State)
    (events : List (Sum LeftEvent RightEvent)) :
    (parallelComposite left right).advance (leftState, rightState) events =
      (left.advance leftState (leftProjection events)).bind fun finalLeft =>
        (right.advance rightState (rightProjection events)).map fun finalRight =>
          (finalLeft, finalRight) := by
  induction events generalizing leftState rightState with
  | nil => rfl
  | cons event events inductionHypothesis =>
      cases event with
      | inl leftEvent =>
          simp only [advance, parallelComposite, leftProjection_inl_cons,
            rightProjection_inl_cons]
          cases leftStep : left.step leftState leftEvent with
          | none => rfl
          | some nextLeft =>
              simp only [Option.map_some, Option.bind_some]
              exact inductionHypothesis nextLeft rightState
      | inr rightEvent =>
          simp only [advance, parallelComposite, leftProjection_inr_cons,
            rightProjection_inr_cons]
          cases rightStep : right.step rightState rightEvent with
          | none =>
              simp only [Option.map_none, Option.bind_none]
              cases leftRun : left.advance leftState (leftProjection events) <;>
                simp
          | some nextRight =>
              simp only [Option.map_some, Option.bind_some]
              exact inductionHypothesis leftState nextRight

/-- Main fusion theorem: the streaming product implements the extensional
product of the two projection collectors. -/
theorem toCollector_parallelComposite_collect
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left : StreamingWitnessCollector.{uLeftEvent, uLeftContainer, uLeftState}
      LeftEvent)
    (right : StreamingWitnessCollector.{uRightEvent, uRightContainer, uRightState}
      RightEvent)
    (events : List (Sum LeftEvent RightEvent)) :
    (parallelComposite left right).toCollector.collect events =
      ((left.toCollector.onLeft (RightEvent := RightEvent)).prod
        (right.toCollector.onRight (LeftEvent := LeftEvent))).collect events := by
  rw [show (parallelComposite left right).toCollector.collect events =
      ((parallelComposite left right).run events).map
        (parallelComposite left right).finish by rfl]
  rw [show (parallelComposite left right).run events =
      (parallelComposite left right).advance
        (left.initial, right.initial) events by rfl]
  rw [parallelComposite_advance]
  unfold WitnessCollector.prod WitnessCollector.onLeft
    WitnessCollector.onRight toCollector run
  cases leftRun : left.advance left.initial (leftProjection events) <;>
    cases rightRun : right.advance right.initial (rightProjection events) <;>
      simp [leftRun, rightRun, parallelComposite]

/-! ## Small controls -/

/-- A total streaming counter. -/
def counter (Event : Type uEvent) :
    StreamingWitnessCollector.{uEvent, 0, 0} Event where
  Container := Nat
  State := Nat
  initial := 0
  step := fun count _ => some (count + 1)
  finish := id

/-- Positive control: the fused product counts each component in one pass. -/
example :
    (parallelComposite (counter Nat) (counter Bool)).toCollector.collect
        [.inl 3, .inr true, .inl 5] =
      (some ((2, 1) : Nat × Nat) : Option (Nat × Nat)) :=
  rfl

/-- Negative control: events are not accidentally sent to both components. -/
example :
    (parallelComposite (counter Nat) (counter Bool)).toCollector.collect
        [.inr true] ≠ (some ((1, 1) : Nat × Nat) : Option (Nat × Nat)) := by
  change some ((0, 1) : Nat × Nat) ≠ some ((1, 1) : Nat × Nat)
  decide

end StreamingWitnessCollector

end Mettapedia.GSLT.Dynamics
