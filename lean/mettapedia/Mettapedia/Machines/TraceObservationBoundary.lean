import Mettapedia.Machines.RunObservation

/-!
# Trace observation boundaries

A replay checker can validate only information that an execution trace
actually exports.  This module isolates three erasures that occur at common
native trace boundaries:

* flattening a causal receipt retains event occurrences but forgets edges;
* exporting an observation without its demand annotation forgets both the
  demand role and expected type;
* reporting an external interruption without its frontier forgets the live
  states that remained when execution stopped.

The counterexamples below are constructive non-injectivity results.  They
prevent a checker from reconstructing any of these witnesses solely from the
corresponding erased observation.
-/

namespace Mettapedia.Machines

/-! ## Causal edges -/

/-- One event occurrence together with its immediate causal predecessors. -/
structure CausalEvent (Event : Type) where
  event : Event
  directCauses : List Event
deriving DecidableEq, Repr

/-- A finite causal receipt.  Roots identify the events directly supporting
the published observation; `events` retains the immediate-edge relation. -/
structure CausalReceipt (Event : Type) where
  roots : List Event
  events : List (CausalEvent Event)
deriving DecidableEq, Repr

namespace CausalReceipt

/-- The occurrence-preserving support currently visible to a flattened trace.
The order and multiplicity of event occurrences survive; causal edges do not. -/
def flattenedSupport (receipt : CausalReceipt Event) : List Event :=
  receipt.events.map CausalEvent.event

private def independentReceipt : CausalReceipt Nat where
  roots := [2]
  events :=
    [ { event := 1, directCauses := [] }
    , { event := 2, directCauses := [] } ]

private def dependentReceipt : CausalReceipt Nat where
  roots := [2]
  events :=
    [ { event := 1, directCauses := [] }
    , { event := 2, directCauses := [1] } ]

/-- Positive discriminator: flattening retains both event occurrences in
their exported order. -/
example : dependentReceipt.flattenedSupport = [1, 2] := rfl

/-- Negative discriminator: an independent pair and a causal chain have the
same flattened support. -/
example : independentReceipt.flattenedSupport =
    dependentReceipt.flattenedSupport := rfl

theorem independentReceipt_ne_dependentReceipt :
    independentReceipt ≠ dependentReceipt := by
  intro equal
  have eventsEqual := congrArg CausalReceipt.events equal
  simp [independentReceipt, dependentReceipt] at eventsEqual

/-- Consequently, no decoder from flattened event support can recover the
causal receipt for every input. -/
theorem flattenedSupport_not_injective :
    ¬ Function.Injective
      (flattenedSupport : CausalReceipt Nat → List Nat) := by
  intro injective
  exact independentReceipt_ne_dependentReceipt
    (injective (by rfl))

end CausalReceipt

/-! ## Demand annotations -/

/-- Whether a cell observation was demanded while matching a left-hand side
or while evaluating the selected right-hand side. -/
inductive DemandRole where
  | lhs
  | rhs
deriving DecidableEq, Repr

/-- Candidate-local information required to replay why an event was demanded. -/
structure DemandAnnotation (Event ExpectedType : Type) where
  event : Event
  role : DemandRole
  expectedType : ExpectedType
deriving DecidableEq, Repr

namespace DemandAnnotation

/-- The event-only projection used when role and expected type are absent from
the wire observation. -/
def erase (annotation : DemandAnnotation Event ExpectedType) : Event :=
  annotation.event

private def lhsDemand : DemandAnnotation Nat Bool :=
  { event := 7, role := .lhs, expectedType := false }

private def rhsDemand : DemandAnnotation Nat Bool :=
  { event := 7, role := .rhs, expectedType := false }

private def otherTypeDemand : DemandAnnotation Nat Bool :=
  { event := 7, role := .lhs, expectedType := true }

/-- Positive discriminator: erasure retains the referenced event occurrence. -/
example : lhsDemand.erase = 7 := rfl

/-- The event-only projection cannot distinguish left- from right-hand-side
demand. -/
theorem erase_role_not_injective :
    ¬ Function.Injective
      (erase : DemandAnnotation Nat Bool → Nat) := by
  intro injective
  have equalAnnotations : lhsDemand = rhsDemand :=
    injective (by rfl)
  have equalRoles := congrArg DemandAnnotation.role equalAnnotations
  cases equalRoles

/-- Nor can the same projection reconstruct the expected type. -/
theorem erase_expectedType_not_injective :
    ¬ Function.Injective
      (erase : DemandAnnotation Nat Bool → Nat) := by
  intro injective
  have equalAnnotations : lhsDemand = otherTypeDemand :=
    injective (by rfl)
  have equalTypes := congrArg DemandAnnotation.expectedType equalAnnotations
  simp [lhsDemand, otherTypeDemand] at equalTypes

end DemandAnnotation

/-! ## Interrupted frontiers -/

/-- A resource-interrupted execution together with the live frontier known to
the producer.  The existing external observation retains the answers and
reason but may omit `pending`. -/
structure InterruptedRunWitness (State Answer : Type) where
  answers : List (Answer × List Nat)
  reason : ResourceInterruption
  pending : List State
deriving DecidableEq, Repr

namespace InterruptedRunWitness

/-- Erase a producer-side interrupted frontier to the public run observation. -/
def erase (witness : InterruptedRunWitness State Answer) :
    RunObservation State Answer where
  answers := witness.answers
  stop := .interrupted witness.reason

private def waitingAtOne : InterruptedRunWitness Nat Nat where
  answers := [(7, [0])]
  reason := .fuelExhausted
  pending := [1]

private def waitingAtTwo : InterruptedRunWitness Nat Nat where
  answers := [(7, [0])]
  reason := .fuelExhausted
  pending := [2]

/-- Positive discriminator: answer occurrences and interruption reason remain
observable after the frontier is erased. -/
example : waitingAtOne.erase.answers = [(7, [0])] := rfl

example : waitingAtOne.erase.stop.externalInterruption =
    some .fuelExhausted := rfl

/-- Negative discriminator: two different live frontiers produce the same
external interruption observation. -/
example : waitingAtOne.erase = waitingAtTwo.erase := rfl

theorem waitingAtOne_ne_waitingAtTwo : waitingAtOne ≠ waitingAtTwo := by
  intro equal
  have pendingEqual := congrArg InterruptedRunWitness.pending equal
  simp [waitingAtOne, waitingAtTwo] at pendingEqual

/-- Therefore an answer-and-reason observation cannot reconstruct the live
frontier of every interrupted execution. -/
theorem erase_not_injective :
    ¬ Function.Injective
      (erase : InterruptedRunWitness Nat Nat → RunObservation Nat Nat) := by
  intro injective
  exact waitingAtOne_ne_waitingAtTwo (injective (by rfl))

end InterruptedRunWitness

end Mettapedia.Machines
