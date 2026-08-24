import Mettapedia.GSLT.Dynamics.ObservationDisciplineCrown

/-!
# Indexed executions observed through an observation discipline

An observation container is not an execution.  This module states the bridge
explicitly for an arbitrary proof-relevant indexed execution family.  An
execution exposes a finite event history, the collector accepts that history,
and the resulting container is then read through the discipline's value map.

The separation is intentional:

* `Execution source target` retains operational proof and endpoints;
* `events` retains the observed occurrences and their order;
* `container` is the collector's `S`-dial result;
* `value` is the `V`-dial readout.

Chronological composition is an additional capability.  When both the
execution and the collector compose, the container-composition theorem is
derived rather than postulated.  Parallel authorization remains in the
execution family that supplies the observed article; equality of containers
or values cannot manufacture it.
-/

namespace Mettapedia.GSLT.Dynamics

universe uEvent uContainer uValue uState uExecution uOtherValue

/-- An exact observation of a proof-relevant indexed execution family. -/
structure IndexedExecutionObservation
    {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (State : Type uState)
    (Execution : State → State → Type uExecution) where
  events : ∀ {source target}, Execution source target → List Event
  container : ∀ {source target}, Execution source target →
    discipline.collection.Container
  collects : ∀ {source target} (execution : Execution source target),
    discipline.collection.collect (events execution) =
      some (container execution)

namespace IndexedExecutionObservation

variable {Event : Type uEvent}
variable {discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event}
variable {State : Type uState} {Execution : State → State → Type uExecution}

/-- Read the declared value from an exact observed execution. -/
def value (observation : IndexedExecutionObservation discipline State Execution)
    {source target : State} (execution : Execution source target) :
    discipline.Value :=
  discipline.readout (observation.container execution)

/-- Observing the retained event history returns exactly the declared value. -/
@[simp] theorem observe_events
    (observation : IndexedExecutionObservation discipline State Execution)
    {source target : State} (execution : Execution source target) :
    discipline.observe (observation.events execution) =
      some (observation.value execution) := by
  simp [ObservationDiscipline.observe, value, observation.collects]

/-- Change only the value dial; execution, event history, and witness
container are retained definitionally. -/
def mapValue
    (observation : IndexedExecutionObservation discipline State Execution)
    (translate : discipline.Value → OtherValue) :
    IndexedExecutionObservation (discipline.mapValue translate) State Execution where
  events := observation.events
  container := observation.container
  collects := observation.collects

@[simp] theorem mapValue_value
    (observation : IndexedExecutionObservation discipline State Execution)
    (translate : discipline.Value → OtherValue)
    {source target : State} (execution : Execution source target) :
    (observation.mapValue translate).value execution =
      translate (observation.value execution) :=
  rfl

/-- The observation is faithful on one indexed execution fibre when equal
values determine equal proof-relevant executions in that fibre. -/
def FaithfulOnExecutions
    (observation : IndexedExecutionObservation discipline State Execution) :
    Prop :=
  ∀ {source target} (first second : Execution source target),
    observation.value first = observation.value second → first = second

/-- One pair of distinct executions with the same value refutes execution
faithfulness.  This is stronger than ordinary `S → V` lossiness: even an
injective readout may fail to reconstruct execution. -/
theorem not_faithfulOnExecutions_of_collision
    (observation : IndexedExecutionObservation discipline State Execution)
    {source target : State} {first second : Execution source target}
    (distinct : first ≠ second)
    (collision : observation.value first = observation.value second) :
    ¬ observation.FaithfulOnExecutions := by
  intro faithful
  exact distinct (faithful first second collision)

/-- Chronological composition of the execution family, with exact agreement
between execution concatenation and concatenation of observed events. -/
structure Chronological
    (observation : IndexedExecutionObservation discipline State Execution) where
  append : ∀ {source middle target},
    Execution source middle → Execution middle target → Execution source target
  events_append : ∀ {source middle target}
      (first : Execution source middle) (second : Execution middle target),
    observation.events (append first second) =
      observation.events first ++ observation.events second

/-- Chronological execution composition is observed by the collector's
declared chronological algebra. -/
theorem Chronological.container_append
    (observation : IndexedExecutionObservation discipline State Execution)
    (collectorChronological : ChronologicalCapability discipline.collection)
    (executionChronological : observation.Chronological)
    {source middle target : State}
    (first : Execution source middle) (second : Execution middle target) :
    collectorChronological.algebra.op
        (observation.container first) (observation.container second) =
      some (observation.container (executionChronological.append first second)) := by
  have collected := collectorChronological.collect_append
    (observation.events first) (observation.events second)
  rw [← executionChronological.events_append first second,
    observation.collects, observation.collects, observation.collects] at collected
  exact collected.symm

end IndexedExecutionObservation

/-! ## Separation canary: exact observation still need not be execution -/

namespace IndexedExecutionObservationCanary

def collector : WitnessCollector Empty where
  Container := Unit
  collect := fun _ => some ()

def discipline : ObservationDiscipline Empty where
  collection := collector
  Value := Unit
  readout := id

/-- Two proof-relevant executions can have the same endpoints and the same
complete observation while remaining different operational articles. -/
inductive Execution : Unit → Unit → Type where
  | left : Execution () ()
  | right : Execution () ()
  deriving DecidableEq

def observation : IndexedExecutionObservation discipline Unit Execution where
  events := fun _ => []
  container := fun _ => ()
  collects := fun _ => rfl

theorem readout_is_faithful : discipline.Faithful := by
  intro first second _
  cases first
  cases second
  rfl

theorem distinct_executions_have_same_container :
    observation.container Execution.left =
      observation.container Execution.right :=
  rfl

theorem distinct_executions_have_same_value :
    observation.value Execution.left = observation.value Execution.right :=
  rfl

/-- A faithful container-to-value readout still does not reconstruct the
execution that produced it. -/
theorem faithful_readout_does_not_imply_execution_faithfulness :
    ¬ observation.FaithfulOnExecutions :=
  observation.not_faithfulOnExecutions_of_collision
    (by decide) distinct_executions_have_same_value

end IndexedExecutionObservationCanary

#print axioms IndexedExecutionObservation.observe_events
#print axioms IndexedExecutionObservation.Chronological.container_append
#print axioms IndexedExecutionObservationCanary.readout_is_faithful
#print axioms IndexedExecutionObservationCanary.faithful_readout_does_not_imply_execution_faithfulness

end Mettapedia.GSLT.Dynamics
