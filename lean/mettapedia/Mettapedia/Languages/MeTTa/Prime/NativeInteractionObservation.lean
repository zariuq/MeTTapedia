import Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture
import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation

/-!
# Capability-indexed observation of intrinsic Prime interaction

An inhabitant of Prime's endpoint-indexed interaction type is already a
proof-relevant execution: it retains both endpoint admissions and the exact
authored event path.  This module uses that inhabited type directly as the
execution family of the general observation architecture.

No interaction is reconstructed from an observation.  A partial collector
may decline an execution while the underlying `Compρ` inhabitant remains
available.  Chronological composition is derived from native interaction
composition and event-path append.  Scalar scheduling is downstream of the
retained occurrence history and therefore cannot authorize a provenance-
sensitive policy when its fibres identify distinct histories.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionObservation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uContainer uValue

variable {theory : GSLT}

/-! ## The intrinsic computation fibre as execution -/

/-- The semantic inhabitant of Prime's interaction type at the unique closed
context.  Its endpoint and event-path evidence is not projected away. -/
abbrev Computation
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    (source target : StagedReflectiveTm 0 0) :=
  (interpretation.computationTy presentation source target) PUnit.unit

/-- The exact event path retained inside an intrinsic interaction
computation. -/
def path
    {interpretation : EndpointInterpretation theory}
    {presentation : InteractionPresentation theory}
    {source target : StagedReflectiveTm 0 0}
    (execution : Computation interpretation presentation source target) :
    EventPath presentation execution.1.1 execution.2.1.1 :=
  execution.2.2

/-- The chronological occurrence history of the intrinsic computation. -/
def events
    {interpretation : EndpointInterpretation theory}
    {presentation : InteractionPresentation theory}
    {source target : StagedReflectiveTm 0 0}
    (execution : Computation interpretation presentation source target) :
    List (Occurrence presentation) :=
  EventPath.events presentation (path execution)

/-- Endpoint erasure exposes the ordinary authorized GSLT path while
retaining the richer execution separately. -/
def erase
    {interpretation : EndpointInterpretation theory}
    {presentation : InteractionPresentation theory}
    {source target : StagedReflectiveTm 0 0}
    (execution : Computation interpretation presentation source target) :
    theory.RewritePath execution.1.1 execution.2.1.1 :=
  (path execution).erase

/-- Event occurrence count survives endpoint-path erasure even though event
identity does not.  This is the exact invariant used by the event-count NIK
refinement below. -/
@[simp] theorem events_length_eq_erase_length
    {interpretation : EndpointInterpretation theory}
    {presentation : InteractionPresentation theory}
    {source target : StagedReflectiveTm 0 0}
    (execution : Computation interpretation presentation source target) :
    (events execution).length = (erase execution).length := by
  have eventsLength : ∀ {first last}
      (eventPath : EventPath presentation first last),
      (EventPath.events presentation eventPath).length =
        EventPath.pathLength presentation eventPath := by
    intro first last eventPath
    induction eventPath with
    | nil => rfl
    | cons event rest inductionHypothesis =>
        simp only [EventPath.events, List.length_cons, EventPath.pathLength]
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using
          congrArg Nat.succ inductionHypothesis
  change (EventPath.events presentation (path execution)).length =
    (path execution).erase.length
  rw [EventPath.erase_length]
  exact eventsLength (path execution)

/-- Native return is the identity interaction at an admitted endpoint. -/
def returnComputation
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    {term : StagedReflectiveTm 0 0} (endpoint : interpretation.Endpoint term) :
    Computation interpretation presentation term term :=
  (interpretation.returnPath presentation endpoint) PUnit.unit

/-- Native interaction composition supplies composition of the intrinsic
execution family. -/
def compose
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    {source middle target : StagedReflectiveTm 0 0}
    (first : Computation interpretation presentation source middle)
    (second : Computation interpretation presentation middle target) :
    Computation interpretation presentation source target :=
  (interpretation.composePath presentation
    (fun _ => first) (fun _ => second)) PUnit.unit

@[simp] theorem events_return
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    {term : StagedReflectiveTm 0 0} (endpoint : interpretation.Endpoint term) :
    events (returnComputation interpretation presentation endpoint) = [] := by
  rfl

/-- Intrinsic composition is observed as chronological concatenation. -/
@[simp] theorem events_compose
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    {source middle target : StagedReflectiveTm 0 0}
    (first : Computation interpretation presentation source middle)
    (second : Computation interpretation presentation middle target) :
    events (compose interpretation presentation first second) =
      events first ++ events second := by
  rcases first with ⟨sourceEndpoint, firstMiddle, firstPath⟩
  rcases second with ⟨secondMiddle, targetEndpoint, secondPath⟩
  have middleEq : firstMiddle = secondMiddle := Subsingleton.elim _ _
  subst secondMiddle
  simp [events, path, compose, EndpointInterpretation.composePath,
    EventPath.events_append]

/-! ## Exact provenance architecture -/

/-- Chronological occurrence provenance retains order and multiplicity as
both its witness container and semantic value. -/
def provenanceDiscipline
    (presentation : InteractionPresentation theory) :
    ObservationDiscipline (Occurrence presentation) where
  collection :=
    { Container := List (Occurrence presentation)
      collect := some }
  Value := List (Occurrence presentation)
  readout := id

/-- Every intrinsic computation is observed without changing its endpoint
indices or proof-relevant carrier. -/
def provenanceObservation
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    IndexedExecutionObservation (provenanceDiscipline presentation)
      (StagedReflectiveTm 0 0) (Computation interpretation presentation) where
  events := events
  container := events
  collects := fun _ => rfl

/-- The capability-indexed observation architecture whose executions are
exactly inhabited Prime interaction fibres. -/
def provenanceArchitecture
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    CapabilityIndexedObservationArchitecture (StagedReflectiveTm 0 0)
      (Computation interpretation presentation) where
  Event := Occurrence presentation
  discipline := provenanceDiscipline presentation
  observation := provenanceObservation interpretation presentation
  domain := ObservationDiscipline.OperationalDomain.reachable
    (provenanceDiscipline presentation)

/-- The provenance collector has chronological list concatenation. -/
def provenanceChronological
    (presentation : InteractionPresentation theory) :
    ChronologicalCapability (provenanceDiscipline presentation).collection where
  algebra := chronologicalListPartialMonoid (Occurrence presentation)
  collect_nil := rfl
  collect_append := fun _ _ => rfl

/-- Native `Compρ` composition is a chronological execution capability for
the exact provenance observation. -/
def computationChronological
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    (provenanceObservation interpretation presentation).Chronological where
  append := compose interpretation presentation
  events_append := events_compose interpretation presentation

/-- Consequently the retained provenance container of a composite is exact
list concatenation. -/
theorem provenance_container_compose
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    {source middle target : StagedReflectiveTm 0 0}
    (first : Computation interpretation presentation source middle)
    (second : Computation interpretation presentation middle target) :
    (provenanceChronological presentation).algebra.op
        ((provenanceObservation interpretation presentation).container first)
        ((provenanceObservation interpretation presentation).container second) =
      some
        ((provenanceObservation interpretation presentation).container
          (compose interpretation presentation first second)) := by
  exact IndexedExecutionObservation.Chronological.container_append
    (provenanceObservation interpretation presentation)
    (provenanceChronological presentation)
    (computationChronological interpretation presentation) first second

/-! ## Partial observation does not gate interaction -/

/-- An intrinsic computation together with the exact result of a possibly
partial witness collector. -/
structure CollectedComputation
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    (discipline : ObservationDiscipline.{_, uContainer, uValue}
      (Occurrence presentation))
    (source target : StagedReflectiveTm 0 0) where
  computation : Computation interpretation presentation source target
  container : discipline.collection.Container
  collected : discipline.collection.collect (events computation) =
    some container

/-- Collected intrinsic computations carry the exact generic observation
architecture, while declined computations remain present in `Computation`. -/
def collectedArchitecture
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory)
    (discipline : ObservationDiscipline.{_, uContainer, uValue}
      (Occurrence presentation)) :
    CapabilityIndexedObservationArchitecture (StagedReflectiveTm 0 0)
      (CollectedComputation interpretation presentation discipline) where
  Event := Occurrence presentation
  discipline := discipline
  observation :=
    { events := fun execution => events execution.computation
      container := fun execution => execution.container
      collects := fun execution => execution.collected }
  domain := ObservationDiscipline.OperationalDomain.reachable discipline

/-! ## Equal endpoints, distinct worlds -/

namespace Canary

open Mettapedia.GSLT.Core.InteractionEvent.Canary

def loopTerm : StagedReflectiveTm 0 0 :=
  .pattern (.apply "prime-observation-loop" [])

def loopInterpretation : EndpointInterpretation loopTheory where
  lower?
    | .pattern _ => some ()
    | _ => none

def loopEndpoint : loopInterpretation.Endpoint loopTerm :=
  ⟨(), rfl⟩

def cheapOccurrence : Occurrence loopPresentation :=
  ⟨(), cheapEvent⟩

def dearOccurrence : Occurrence loopPresentation :=
  ⟨(), dearEvent⟩

theorem cheapOccurrence_ne_dearOccurrence :
    cheapOccurrence ≠ dearOccurrence := by
  intro equal
  have siteEqual := congrArg (fun occurrence => occurrence.2.site) equal
  exact LoopSite.noConfusion siteEqual

def cheapComputation :
    Computation loopInterpretation loopPresentation loopTerm loopTerm :=
  ⟨loopEndpoint, loopEndpoint,
    .cons (site := cheapEvent.site) cheapEvent.evidence
      (.nil (presentation := loopPresentation) ())⟩

def dearComputation :
    Computation loopInterpretation loopPresentation loopTerm loopTerm :=
  ⟨loopEndpoint, loopEndpoint,
    .cons (site := dearEvent.site) dearEvent.evidence
      (.nil (presentation := loopPresentation) ())⟩

@[simp] theorem events_cheapComputation :
    events cheapComputation = [cheapOccurrence] :=
  by rfl

@[simp] theorem events_dearComputation :
    events dearComputation = [dearOccurrence] :=
  by rfl

/-- Equal native and semantic endpoints do not erase occurrence identity. -/
theorem cheap_dear_provenance_distinct :
    events cheapComputation ≠ events dearComputation := by
  intro equal
  have heads : cheapOccurrence = dearOccurrence := by
    exact (List.cons.inj equal).1
  exact cheapOccurrence_ne_dearOccurrence heads

/-- The two retained histories therefore are genuinely different inhabitants
of the same endpoint-indexed Prime interaction type. -/
theorem cheap_dear_computations_distinct :
    cheapComputation ≠ dearComputation := by
  intro equal
  exact cheap_dear_provenance_distinct (congrArg events equal)

abbrev loopArchitecture :=
  provenanceArchitecture loopInterpretation loopPresentation

/-- Event count is a policy-facing scalar, not the retained provenance. -/
def eventCountScheduler : loopArchitecture.SchedulerReadout Nat where
  readout := List.length

theorem eventCountScheduler_isLossy : eventCountScheduler.Lossy := by
  apply eventCountScheduler.lossy_of_collision
    (first := events cheapComputation) (second := events dearComputation)
  · exact cheap_dear_provenance_distinct
  · simp [eventCountScheduler]

/-- After scalarization, equal event counts no longer distinguish the two
proof-relevant interaction worlds. -/
theorem eventCountArchitecture_not_faithfulOnExecutions :
    ¬ eventCountScheduler.toArchitecture.observation.FaithfulOnExecutions := by
  apply eventCountScheduler.toArchitecture.observation
    |>.not_faithfulOnExecutions_of_collision
      cheap_dear_computations_distinct
  change (events cheapComputation).length = (events dearComputation).length
  simp

def beginsAtCheap : List (Occurrence loopPresentation) → Bool
  | [] => false
  | occurrence :: _ =>
      match occurrence.2.site with
      | .cheap => true
      | .dear => false

@[simp] theorem beginsAtCheap_cheap :
    beginsAtCheap (events cheapComputation) = true :=
  by simp [beginsAtCheap, cheapOccurrence, cheapEvent]

@[simp] theorem beginsAtCheap_dear :
    beginsAtCheap (events dearComputation) = false :=
  by simp [beginsAtCheap, dearOccurrence, dearEvent]

/-- Both one-event worlds have equal count, but count cannot implement a
policy that distinguishes their authenticated sites. -/
theorem eventCountScheduler_not_supports_sitePolicy :
    ¬ eventCountScheduler.SupportsPolicy beginsAtCheap := by
  rw [eventCountScheduler.supportsPolicy_iff_constantOnReadoutFibers]
  intro constant
  have cheapMember := loopArchitecture.observed_container_mem cheapComputation
  have dearMember := loopArchitecture.observed_container_mem dearComputation
  have sameCount :
      eventCountScheduler.readout
          (loopArchitecture.discipline.readout
            (loopArchitecture.observation.container cheapComputation)) =
        eventCountScheduler.readout
          (loopArchitecture.discipline.readout
            (loopArchitecture.observation.container dearComputation)) := by
    simp [eventCountScheduler, loopArchitecture, provenanceArchitecture,
      provenanceObservation, provenanceDiscipline]
  have impossible := constant cheapMember dearMember sameCount
  change true = false at impossible
  exact Bool.noConfusion impossible

def nowhere : ObservationDiscipline (Occurrence loopPresentation) where
  collection :=
    { Container := Unit
      collect := fun _ => none }
  Value := Unit
  readout := id

/-- The intrinsic interaction exists even when a selected observer declines
its history. -/
theorem collection_failure_does_not_remove_computation :
    Nonempty
        (Computation loopInterpretation loopPresentation loopTerm loopTerm) ∧
      IsEmpty
        (CollectedComputation loopInterpretation loopPresentation nowhere
          loopTerm loopTerm) := by
  constructor
  · exact ⟨cheapComputation⟩
  · refine ⟨?_⟩
    intro collected
    have impossible := collected.collected
    simp [nowhere] at impossible

end Canary

#print axioms events_compose
#print axioms events_length_eq_erase_length
#print axioms provenance_container_compose
#print axioms Canary.cheap_dear_provenance_distinct
#print axioms Canary.cheap_dear_computations_distinct
#print axioms Canary.eventCountScheduler_isLossy
#print axioms Canary.eventCountArchitecture_not_faithfulOnExecutions
#print axioms Canary.eventCountScheduler_not_supports_sitePolicy
#print axioms Canary.collection_failure_does_not_remove_computation

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionObservation
