import Mettapedia.GSLT.Dynamics.CapabilityGeneratedObservationDomain
import Mettapedia.GSLT.Dynamics.IndexedExecutionObservation

/-!
# Capability-indexed observation architecture

This module is the public factorization interface for observing a
proof-relevant execution family.  It keeps five layers distinct:

* an indexed execution and its exact event history;
* the retained witness container `S`;
* the declared semantic value `V`;
* an optional scheduler readout `Q` from `V`;
* capability-indexed composition on `S`.

The operational domain contains every container produced by an observed
execution, but may additionally contain containers justified by an explicit
capability construction.  A scheduler view never replaces an execution,
witness container, or semantic value.  Its exact authority is characterized
by constancy on the scheduler-readout fibres of the declared domain.

For an arbitrary GSLT and a possibly partial collector, `CollectedPath`
retains precisely the paths whose histories the collector accepts.  Thus
partial observation restricts the observed execution family; it does not turn
collection failure into an operational rejection.
-/

namespace Mettapedia.GSLT.Dynamics

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics.ExecutionPathObservation

universe uEvent uContainer uValue uState uExecution uOtherValue uScore uDecision
universe uTerm

/-- One exact observation architecture over a proof-relevant indexed
execution family.  The event, container, value, and domain choices are data;
none is reconstructed from another layer. -/
structure CapabilityIndexedObservationArchitecture
    (State : Type uState) (Execution : State -> State -> Type uExecution) where
  Event : Type uEvent
  discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event
  observation : IndexedExecutionObservation discipline State Execution
  domain : discipline.OperationalDomain

namespace CapabilityIndexedObservationArchitecture

variable {State : Type uState} {Execution : State -> State -> Type uExecution}

/-- The retained witness-container type of an architecture. -/
abbrev Container
    (architecture : CapabilityIndexedObservationArchitecture State Execution) :=
  architecture.discipline.collection.Container

/-- The declared semantic-value type of an architecture. -/
abbrev Value
    (architecture : CapabilityIndexedObservationArchitecture State Execution) :=
  architecture.discipline.Value

/-- Every exactly observed execution lands in the declared operational
domain.  This follows from collection and `reachable_mem`; it is not another
field that an instance may choose inconsistently. -/
theorem observed_container_mem
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    {source target : State} (execution : Execution source target) :
    architecture.domain.contains
      (architecture.observation.container execution) := by
  apply architecture.domain.reachable_mem
  exact
    ⟨architecture.observation.events execution,
      architecture.observation.collects execution⟩

/-- Collection capabilities remain indexed requests on `S`; merely having an
architecture does not supply any particular algebra. -/
abbrev CollectionCapability
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    (kind : CollectionCapabilityKind) :=
  architecture.discipline.CollectionCapability kind

/-- Change only the semantic-value dial.  Executions, events, retained
containers, the operational domain, and every collection capability remain
definitionally unchanged. -/
def mapValue
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    (translate : architecture.Value -> OtherValue) :
    CapabilityIndexedObservationArchitecture State Execution where
  Event := architecture.Event
  discipline := architecture.discipline.mapValue translate
  observation := architecture.observation.mapValue translate
  domain :=
    { contains := architecture.domain.contains
      reachable_mem := architecture.domain.reachable_mem }

@[simp] theorem mapValue_events
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    (translate : architecture.Value -> OtherValue)
    {source target : State} (execution : Execution source target) :
    (architecture.mapValue translate).observation.events execution =
      architecture.observation.events execution :=
  rfl

@[simp] theorem mapValue_container
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    (translate : architecture.Value -> OtherValue)
    {source target : State} (execution : Execution source target) :
    (architecture.mapValue translate).observation.container execution =
      architecture.observation.container execution :=
  rfl

@[simp] theorem mapValue_value
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    (translate : architecture.Value -> OtherValue)
    {source target : State} (execution : Execution source target) :
    (architecture.mapValue translate).observation.value execution =
      translate (architecture.observation.value execution) :=
  rfl

/-- Any previously supplied collection capability survives a value change
without transport or reconstruction. -/
def mapValueCollectionCapability
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    (translate : architecture.Value -> OtherValue)
    {kind : CollectionCapabilityKind}
    (capability : architecture.CollectionCapability kind) :
    (architecture.mapValue translate).CollectionCapability kind :=
  capability

/-! ## Scheduler views are a separate, optionally lossy layer -/

/-- A scheduler view reads a policy-facing value `Q` from the semantic value
`V`.  No order, maximization rule, or selection policy is bundled into the
view. -/
structure SchedulerReadout
    (architecture : CapabilityIndexedObservationArchitecture State Execution)
    (Score : Type uScore) where
  readout : architecture.Value -> Score

namespace SchedulerReadout

variable {architecture :
  CapabilityIndexedObservationArchitecture State Execution}
variable {Score : Type uScore}

/-- Regard a scheduler view as changing only the value dial of the same
architecture. -/
def toArchitecture (view : SchedulerReadout architecture Score) :
    CapabilityIndexedObservationArchitecture State Execution :=
  architecture.mapValue view.readout

/-- The scheduler score observed on one execution, factored through the full
semantic value. -/
def observedScore (view : SchedulerReadout architecture Score)
    {source target : State} (execution : Execution source target) : Score :=
  view.readout (architecture.observation.value execution)

@[simp] theorem observedScore_factorization
    (view : SchedulerReadout architecture Score)
    {source target : State} (execution : Execution source target) :
    view.observedScore execution =
      view.readout
        (architecture.discipline.readout
          (architecture.observation.container execution)) :=
  rfl

/-- A scheduler readout is lossy when it identifies distinct semantic values.
This is independent of loss between executions and witness containers or
between witness containers and semantic values. -/
def Lossy (view : SchedulerReadout architecture Score) : Prop :=
  ¬ Function.Injective view.readout

/-- One scheduler collision proves lossiness. -/
theorem lossy_of_collision (view : SchedulerReadout architecture Score)
    {first second : architecture.Value}
    (distinct : Not (first = second))
    (collision : view.readout first = view.readout second) :
    view.Lossy := by
  intro injective
  exact distinct (injective collision)

/-- A lossy scheduler score cannot reconstruct the semantic value. -/
theorem no_value_reconstruction_of_lossy
    (view : SchedulerReadout architecture Score) (lossy : view.Lossy) :
    ¬ ∃ recover : Score -> architecture.Value,
      Function.LeftInverse recover view.readout := by
  rintro ⟨recover, leftInverse⟩
  exact lossy leftInverse.injective

/-- A policy on retained containers is supported by a scheduler view when it
factors through `S -> V -> Q` on the declared operational domain. -/
def SupportsPolicy (view : SchedulerReadout architecture Score)
    (policy : architecture.Container -> Decision) : Prop :=
  view.toArchitecture.domain.SupportsPolicy policy

/-- A Nat-valued score on retained containers supports exact maximum
selection when it factors through the scheduler view on the declared domain. -/
def SupportsMaxSelection (view : SchedulerReadout architecture Score)
    (score : architecture.Container -> Nat) : Prop :=
  view.toArchitecture.domain.SupportsMaxSelection score

/-- Exact scheduler-policy criterion for the full factorization.  Equal `Q`
readouts may be identified precisely when the target policy also identifies
them on every domain member. -/
theorem supportsPolicy_iff_constantOnReadoutFibers [Nonempty Decision]
    (view : SchedulerReadout architecture Score)
    (policy : architecture.Container -> Decision) :
    view.SupportsPolicy policy <->
      ∀ {first second : architecture.Container},
        architecture.domain.contains first ->
        architecture.domain.contains second ->
        view.readout (architecture.discipline.readout first) =
          view.readout (architecture.discipline.readout second) ->
        policy first = policy second := by
  exact ObservationDiscipline.OperationalDomain.supportsPolicy_iff_constantOnReadoutFibers
    view.toArchitecture.domain policy

/-- Exact maximum-selection criterion through `S -> V -> Q`. -/
theorem supportsMaxSelection_iff_constantOnReadoutFibers
    (view : SchedulerReadout architecture Score)
    (score : architecture.Container -> Nat) :
    view.SupportsMaxSelection score <->
      ∀ {first second : architecture.Container},
        architecture.domain.contains first ->
        architecture.domain.contains second ->
        view.readout (architecture.discipline.readout first) =
          view.readout (architecture.discipline.readout second) ->
        score first = score second := by
  exact
    ObservationDiscipline.OperationalDomain.supportsMaxSelection_iff_constantOnReadoutFibers
      view.toArchitecture.domain score

/-- Scheduler policy support and maximum-selection support have the same
information criterion on the declared domain. -/
theorem supportsMaxSelection_iff_supportsPolicy
    (view : SchedulerReadout architecture Score)
    (score : architecture.Container -> Nat) :
    view.SupportsMaxSelection score <-> view.SupportsPolicy score :=
  ObservationDiscipline.OperationalDomain.supportsMaxSelection_iff_supportsPolicy
    view.toArchitecture.domain score

/-- Scheduler scalarization retains whichever collection capability was
actually supplied; it cannot create a missing capability. -/
def collectionCapability (view : SchedulerReadout architecture Score)
    {kind : CollectionCapabilityKind}
    (capability : architecture.CollectionCapability kind) :
    view.toArchitecture.CollectionCapability kind :=
  capability

end SchedulerReadout

end CapabilityIndexedObservationArchitecture

/-! ## Accepted event histories -/

namespace CollectedEventHistory

/-- A finite event history together with the exact witness container accepted
by a possibly partial collector. -/
structure CollectedHistory {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event) where
  events : List Event
  container : discipline.collection.Container
  collected : discipline.collection.collect events = some container

/-- Accepted histories form an indexed execution family with one state.  The
trivial endpoint index is intentional; the proof-relevant execution is the
history and its collection witness. -/
abbrev Execution {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event) :
    Unit -> Unit -> Type (max uEvent uContainer) :=
  fun _ _ => CollectedHistory discipline

def observation {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event) :
    IndexedExecutionObservation discipline Unit (Execution discipline) where
  events := fun execution => execution.events
  container := fun execution => execution.container
  collects := fun execution => execution.collected

/-- The canonical architecture on all accepted finite histories. -/
def architecture {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event) :
    CapabilityIndexedObservationArchitecture Unit (Execution discipline) where
  Event := Event
  discipline := discipline
  observation := observation discipline
  domain := ObservationDiscipline.OperationalDomain.reachable discipline

end CollectedEventHistory

/-! ## Arbitrary GSLT paths with partial collection -/

namespace CollectedGSLTPath

/-- A GSLT execution path together with the exact witness container collected
from its event history.  A partial collector simply has no inhabitant for a
declined path. -/
structure CollectedPath (system : GSLT.{uTerm})
    (discipline : GSLTObservation system)
    (source target : system.Term) where
  path : ExecutionPath system source target
  container : discipline.collection.Container
  collected : discipline.collection.collect
      (ExecutionPathObservation.events path) = some container

/-- Collected paths carry their exact indexed execution observation. -/
def observation (system : GSLT.{uTerm}) (discipline : GSLTObservation system) :
    IndexedExecutionObservation discipline system.Term
      (CollectedPath system discipline) where
  events := fun execution => ExecutionPathObservation.events execution.path
  container := fun execution => execution.container
  collects := fun execution => execution.collected

/-- The canonical observation architecture of the accepted paths of one GSLT
and one discipline. -/
def architecture (system : GSLT.{uTerm})
    (discipline : GSLTObservation system) :
    CapabilityIndexedObservationArchitecture system.Term
      (CollectedPath system discipline) where
  Event := system.LabeledStep
  discipline := discipline
  observation := observation system discipline
  domain := ObservationDiscipline.OperationalDomain.reachable discipline

/-- A concrete collection equation constructs an observed GSLT path. -/
def ofCollected {system : GSLT.{uTerm}} {discipline : GSLTObservation system}
    {source target : system.Term}
    (path : ExecutionPath system source target)
    (container : discipline.collection.Container)
    (collected : discipline.collection.collect
      (ExecutionPathObservation.events path) = some container) :
    CollectedPath system discipline source target :=
  ⟨path, container, collected⟩

end CollectedGSLTPath

/-! ## Positive and negative controls for all factorization layers -/

namespace CapabilityIndexedObservationCanary

open CapabilityIndexedObservationArchitecture

/-- Trace executions keep exact event order at the execution layer. -/
abbrev TraceExecution : Unit -> Unit -> Type := fun _ _ => List Canary.Event

/-- The full-provenance architecture has identity `S -> V`; execution,
container, and value nevertheless remain separately named layers. -/
def provenanceArchitecture :
    CapabilityIndexedObservationArchitecture Unit TraceExecution where
  Event := Canary.Event
  discipline := Canary.provenance
  observation :=
    { events := id
      container := id
      collects := fun _ => rfl }
  domain := ObservationDiscipline.OperationalDomain.reachable Canary.provenance

/-- A scheduler that sees only history length. -/
def lengthScheduler :
    provenanceArchitecture.SchedulerReadout Nat where
  readout := List.length

def beginsLeft : List Canary.Event -> Bool
  | Canary.Event.left :: _ => true
  | _ => false

@[simp] theorem lengthScheduler_observes_two :
    lengthScheduler.observedScore (source := ()) (target := ())
      [Canary.Event.left, Canary.Event.right] = 2 :=
  rfl

/-- The length scheduler is lossy at the `V -> Q` layer. -/
theorem lengthScheduler_isLossy : lengthScheduler.Lossy := by
  apply lengthScheduler.lossy_of_collision
      (first := [Canary.Event.left, Canary.Event.right])
      (second := [Canary.Event.right, Canary.Event.left])
  · intro same
    have heads := congrArg List.head? same
    simp at heads
  · rfl

/-- Length is nevertheless sufficient for the policy it actually exposes. -/
theorem lengthScheduler_supports_lengthPolicy :
    lengthScheduler.SupportsPolicy List.length := by
  refine ⟨id, ?_⟩
  intro container member
  rfl

/-- The same scheduler cannot implement an order-sensitive policy.  Both
histories are reachable and have equal scheduler score, but their first
events differ. -/
theorem lengthScheduler_not_supports_beginsLeft :
    ¬ lengthScheduler.SupportsPolicy beginsLeft := by
  rw [lengthScheduler.supportsPolicy_iff_constantOnReadoutFibers]
  intro constant
  have leftReachable :
      provenanceArchitecture.domain.contains
        [Canary.Event.left, Canary.Event.right] :=
    ⟨[Canary.Event.left, Canary.Event.right], rfl⟩
  have rightReachable :
      provenanceArchitecture.domain.contains
        [Canary.Event.right, Canary.Event.left] :=
    ⟨[Canary.Event.right, Canary.Event.left], rfl⟩
  have impossible := constant leftReachable rightReachable rfl
  simp [beginsLeft] at impossible

/- A collector that rejects every history yields no collected path, while
the underlying reflexive GSLT execution still exists.  Observation failure is
therefore not operational rejection. -/
namespace PartialCollection

abbrev system : GSLT := GSLT.discrete Unit

def nowhere : GSLTObservation system where
  collection :=
    { Container := Unit
      collect := fun _ => none }
  Value := Unit
  readout := id

theorem raw_reflexive_path_exists :
    Nonempty (ExecutionPath system () ()) :=
  ⟨.refl ()⟩

theorem no_collected_reflexive_path :
    IsEmpty (CollectedGSLTPath.CollectedPath system nowhere () ()) :=
  ⟨by
    intro execution
    have impossible := execution.collected
    simp [nowhere] at impossible⟩

theorem collection_failure_does_not_remove_execution :
    Nonempty (ExecutionPath system () ()) ∧
      IsEmpty (CollectedGSLTPath.CollectedPath system nowhere () ()) :=
  ⟨raw_reflexive_path_exists, no_collected_reflexive_path⟩

end PartialCollection

/-- The four non-collapse controls coexist: an exact semantic readout can
still forget execution identity; equal values can arise from different
witness-container designs; a scheduler view can forget semantic values; and
such a lossy scheduler may support one policy while refusing another. -/
theorem factorization_layers_are_independent :
    (¬ IndexedExecutionObservationCanary.observation.FaithfulOnExecutions) ∧
      (¬ ∃ recover : Nat -> List Canary.Event,
        Canary.countCollection.FactorsThrough Canary.provenanceCollection
          recover) ∧
      lengthScheduler.Lossy ∧
      lengthScheduler.SupportsPolicy List.length ∧
      ¬ lengthScheduler.SupportsPolicy beginsLeft :=
  ⟨IndexedExecutionObservationCanary.faithful_readout_does_not_imply_execution_faithfulness,
    Canary.no_count_to_provenance_factorization,
    lengthScheduler_isLossy,
    lengthScheduler_supports_lengthPolicy,
    lengthScheduler_not_supports_beginsLeft⟩

end CapabilityIndexedObservationCanary

#print axioms CapabilityIndexedObservationArchitecture.observed_container_mem
#print axioms CapabilityIndexedObservationArchitecture.SchedulerReadout.supportsPolicy_iff_constantOnReadoutFibers
#print axioms CapabilityIndexedObservationArchitecture.SchedulerReadout.supportsMaxSelection_iff_constantOnReadoutFibers
#print axioms CollectedGSLTPath.observation
#print axioms CapabilityIndexedObservationCanary.lengthScheduler_isLossy
#print axioms CapabilityIndexedObservationCanary.lengthScheduler_supports_lengthPolicy
#print axioms CapabilityIndexedObservationCanary.lengthScheduler_not_supports_beginsLeft
#print axioms CapabilityIndexedObservationCanary.PartialCollection.collection_failure_does_not_remove_execution
#print axioms CapabilityIndexedObservationCanary.factorization_layers_are_independent

end Mettapedia.GSLT.Dynamics
