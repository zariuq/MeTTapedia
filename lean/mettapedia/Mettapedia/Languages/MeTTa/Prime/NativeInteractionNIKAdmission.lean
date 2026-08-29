import Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionNIKBoundary

/-!
# NIK admission for intrinsic Prime interaction executions

Prime's intrinsic interaction family retains admitted endpoints and exact
authored event occurrences.  Ordinary GSLT rewrite paths are a sound but
provenance-losing realization of that family.

This module instantiates the generic indexed-execution NIK doctrine twice:

* positively, endpoint-path erasure preserves the declared event-count
  observation and therefore supplies an observation-decorated refinement
  cell that may be retained at a dependency revision;
* negatively, the same erasure cell cannot be decorated by exact occurrence
  provenance, nor by a site-sensitive policy, because the cheap and dear
  interaction worlds have equal erasures.

The target still retains endpoint admissions together with its rewrite path.
Only occurrence sites and event evidence are erased.  Profitability is absent
from this admission: a separate policy may inspect a compatible observation
after semantic adequacy has been established.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionNIKAdmission

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionObservation

variable {theory : GSLT}

/-! ## Intrinsic and erased execution families -/

/-- Endpoint admission is the state meaning retained by both execution
families.  This is nontrivial because a partial interpretation may leave a
native term without any endpoint. -/
def EndpointMeaning (interpretation : EndpointInterpretation theory)
    (term : StagedReflectiveTm 0 0) : Prop :=
  Nonempty (interpretation.Endpoint term)

/-- Endpoint-path realization of an intrinsic interaction.  Both endpoint
admissions survive; only event sites and occurrence evidence are forgotten. -/
def ErasedComputation
    (interpretation : EndpointInterpretation theory)
    (source target : StagedReflectiveTm 0 0) : Type _ :=
  Σ sourceEndpoint : interpretation.Endpoint source,
    Σ targetEndpoint : interpretation.Endpoint target,
      theory.RewritePath sourceEndpoint.1 targetEndpoint.1

/-- Sound endpoint-path erasure of one intrinsic computation. -/
def eraseComputation
    {interpretation : EndpointInterpretation theory}
    {presentation : InteractionPresentation theory}
    {source target : StagedReflectiveTm 0 0}
    (execution : Computation interpretation presentation source target) :
    ErasedComputation interpretation source target :=
  ⟨execution.1, execution.2.1, erase execution⟩

def intrinsicOperational
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    IndexedOperationalObject where
  State := StagedReflectiveTm 0 0
  Execution := Computation interpretation presentation
  Meaning := EndpointMeaning interpretation

def erasedOperational
    (interpretation : EndpointInterpretation theory) :
    IndexedOperationalObject where
  State := StagedReflectiveTm 0 0
  Execution := ErasedComputation interpretation
  Meaning := EndpointMeaning interpretation

/-- Event erasure is a genuine equipment cell and semantic NIK refinement,
not merely a function on completed traces. -/
def erasureRefinement
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    IndexedRefinement (intrinsicOperational interpretation presentation)
      (erasedOperational interpretation) where
  mapState := _root_.id
  mapExecution := eraseComputation
  preservesMeaning := fun _ meaningful => meaningful

/-! ## Exact positive observation: event count -/

/-- Event count changes only the value dial of the exact provenance
architecture.  The intrinsic execution and retained occurrence list remain
unchanged. -/
def eventCountArchitecture
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    CapabilityIndexedObservationArchitecture (StagedReflectiveTm 0 0)
      (Computation interpretation presentation) :=
  (provenanceArchitecture interpretation presentation).mapValue List.length

def intrinsicEventCount
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    IndexedObservedOperationalObject Nat :=
  IndexedObservedOperationalObject.ofArchitecture
    (eventCountArchitecture interpretation presentation)
    (EndpointMeaning interpretation)

def erasedEventCount
    (interpretation : EndpointInterpretation theory) :
    IndexedObservedOperationalObject Nat where
  operational := erasedOperational interpretation
  observe := fun execution => some execution.2.2.length

/-- The erasure cell is compatible with event count on every intrinsic
interaction, not only on the separating canary. -/
theorem eventCountCompatible
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    IndexedObservedRefinement.Compatible
      (source := intrinsicEventCount interpretation presentation)
      (target := erasedEventCount interpretation)
      (erasureRefinement interpretation presentation) := by
  intro source target execution
  change some (erase execution).length = some (events execution).length
  rw [events_length_eq_erase_length]

/-- Exact event-count compatibility decorates the semantic erasure cell with
the observation square required by NIK admission. -/
def eventCountRefinement
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    IndexedObservedRefinement
      (intrinsicEventCount interpretation presentation)
      (erasedEventCount interpretation) where
  refinement := erasureRefinement interpretation presentation
  commutes := eventCountCompatible interpretation presentation

theorem eventCount_square_exists_over_erasure
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    Nonempty
      { square : IndexedObservedRefinement
          (intrinsicEventCount interpretation presentation)
          (erasedEventCount interpretation) //
        square.refinement = erasureRefinement interpretation presentation } :=
  (IndexedObservedRefinement.compatible_iff_exists_square_over
    (source := intrinsicEventCount interpretation presentation)
    (target := erasedEventCount interpretation)
    (erasureRefinement interpretation presentation)).mp
      (eventCountCompatible interpretation presentation)

/-! ## Exact negative observation: provenance cannot descend -/

def intrinsicProvenance
    (interpretation : EndpointInterpretation theory)
    (presentation : InteractionPresentation theory) :
    IndexedObservedOperationalObject (List (Occurrence presentation)) :=
  IndexedObservedOperationalObject.ofArchitecture
    (provenanceArchitecture interpretation presentation)
    (EndpointMeaning interpretation)

/-- A proposed target observation that consults only the erased rewrite
path. -/
def erasedPathObservation
    (interpretation : EndpointInterpretation theory)
    {Value : Type}
    (readout : ∀ {source target : theory.Term},
      theory.RewritePath source target → Option Value) :
    IndexedObservedOperationalObject Value where
  operational := erasedOperational interpretation
  observe := fun execution => readout execution.2.2

namespace Canary

open Mettapedia.GSLT.Core.InteractionEvent.Canary
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionObservation.Canary
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionNIKBoundary.Canary

/-- No erased-path readout makes the exact erasure cell compatible with
occurrence provenance.  This is the observation-square form of provenance
nonfactorization. -/
theorem erasure_not_provenanceCompatible
    (readout : ∀ {source target : loopTheory.Term},
      loopTheory.RewritePath source target →
        Option (List (Occurrence loopPresentation))) :
    ¬ IndexedObservedRefinement.Compatible
      (source := intrinsicProvenance loopInterpretation loopPresentation)
      (target := erasedPathObservation loopInterpretation readout)
      (erasureRefinement loopInterpretation loopPresentation) := by
  intro compatible
  have cheap := compatible cheapComputation
  have dear := compatible dearComputation
  change readout (erase cheapComputation) =
    some (events cheapComputation) at cheap
  change readout (erase dearComputation) =
    some (events dearComputation) at dear
  have sameReadout :
      readout (erase cheapComputation) =
        readout (erase dearComputation) := by
    exact congrArg (fun path => readout path) cheap_dear_erasure_equal
  have sameEvents :
      some (events cheapComputation) =
        some (events dearComputation) :=
    cheap.symm.trans (sameReadout.trans dear)
  exact cheap_dear_provenance_distinct (Option.some.inj sameEvents)

/-- Hence there is no provenance-preserving NIK observation square over the
fixed semantic erasure cell. -/
theorem no_provenance_square_over_erasure
    (readout : ∀ {source target : loopTheory.Term},
      loopTheory.RewritePath source target →
        Option (List (Occurrence loopPresentation))) :
    ¬ Nonempty
      { square : IndexedObservedRefinement
          (intrinsicProvenance loopInterpretation loopPresentation)
          (erasedPathObservation loopInterpretation readout) //
        square.refinement =
          erasureRefinement loopInterpretation loopPresentation } := by
  intro square
  exact erasure_not_provenanceCompatible readout
    ((IndexedObservedRefinement.compatible_iff_exists_square_over
      (source := intrinsicProvenance loopInterpretation loopPresentation)
      (target := erasedPathObservation loopInterpretation readout)
      (erasureRefinement loopInterpretation loopPresentation)).mpr square)

/-- The site-sensitive policy viewed as an observation of the intrinsic
execution family. -/
def intrinsicSitePolicy : IndexedObservedOperationalObject Bool where
  operational := intrinsicOperational loopInterpretation loopPresentation
  observe := fun execution => some (beginsAtCheap (events execution))

/-- Even the Boolean policy cannot decorate endpoint erasure.  Thus the
negative boundary is not an artifact of asking to reconstruct the complete
event list. -/
theorem erasure_not_sitePolicyCompatible
    (readout : ∀ {source target : loopTheory.Term},
      loopTheory.RewritePath source target → Option Bool) :
    ¬ IndexedObservedRefinement.Compatible
      (source := intrinsicSitePolicy)
      (target := erasedPathObservation loopInterpretation readout)
      (erasureRefinement loopInterpretation loopPresentation) := by
  intro compatible
  have cheap := compatible cheapComputation
  have dear := compatible dearComputation
  change readout (erase cheapComputation) =
    some (beginsAtCheap (events cheapComputation)) at cheap
  change readout (erase dearComputation) =
    some (beginsAtCheap (events dearComputation)) at dear
  have sameReadout :
      readout (erase cheapComputation) =
        readout (erase dearComputation) :=
    congrArg (fun path => readout path) cheap_dear_erasure_equal
  have sameDecision :
      some (beginsAtCheap (events cheapComputation)) =
        some (beginsAtCheap (events dearComputation)) :=
    cheap.symm.trans (sameReadout.trans dear)
  have impossible : true = false := by
    simpa only [beginsAtCheap_cheap, beginsAtCheap_dear] using
      Option.some.inj sameDecision
  exact Bool.noConfusion impossible

theorem no_sitePolicy_square_over_erasure
    (readout : ∀ {source target : loopTheory.Term},
      loopTheory.RewritePath source target → Option Bool) :
    ¬ Nonempty
      { square : IndexedObservedRefinement intrinsicSitePolicy
          (erasedPathObservation loopInterpretation readout) //
        square.refinement =
          erasureRefinement loopInterpretation loopPresentation } := by
  intro square
  exact erasure_not_sitePolicyCompatible readout
    ((IndexedObservedRefinement.compatible_iff_exists_square_over
      (source := intrinsicSitePolicy)
      (target := erasedPathObservation loopInterpretation readout)
      (erasureRefinement loopInterpretation loopPresentation)).mpr square)

/-! ## Revision currentness is orthogonal to the observation square -/

def dependencies : DependencySystem where
  Revision := Bool × Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision.1

def admittedRevision : dependencies.Revision := (false, false)

def eventCountAdmission :
    IndexedObservedAdmittedAt dependencies admittedRevision
      (intrinsicEventCount loopInterpretation loopPresentation)
      (erasedEventCount loopInterpretation) where
  refinement := eventCountRefinement loopInterpretation loopPresentation

/-- Changing an irrelevant component preserves the exact selected dependency
view and therefore permits activation. -/
def activeAfterIrrelevantChange :
    eventCountAdmission.Active (false, true) :=
  eventCountAdmission.activate (by intro dependency; rfl)

@[simp] theorem active_run_is_endpoint_identity
    (term : StagedReflectiveTm 0 0) :
    activeAfterIrrelevantChange.run term = term :=
  rfl

/-- Active proof-relevant execution mapping is the already-retained erasure;
activation performs no new checking or reconstruction. -/
@[simp] theorem active_mapExecution_is_erasure
    {source target : StagedReflectiveTm 0 0}
    (execution : Computation loopInterpretation loopPresentation source target) :
    activeAfterIrrelevantChange.mapExecution execution =
      eraseComputation execution :=
  rfl

theorem active_eventCount_agrees
    {source target : StagedReflectiveTm 0 0}
    (execution : Computation loopInterpretation loopPresentation source target) :
    (erasedEventCount loopInterpretation).observe
        (activeAfterIrrelevantChange.mapExecution execution) =
      (intrinsicEventCount loopInterpretation loopPresentation).observe
        execution :=
  activeAfterIrrelevantChange.observationAgreement execution

/-- Changing the selected dependency component prevents activation. -/
theorem relevant_change_prevents_activation :
    ¬ eventCountAdmission.Active (true, false) := by
  intro active
  have changed := active.current ()
  change false = true at changed
  exact Bool.noConfusion changed

end Canary

#print axioms eventCountCompatible
#print axioms eventCount_square_exists_over_erasure
#print axioms Canary.erasure_not_provenanceCompatible
#print axioms Canary.no_provenance_square_over_erasure
#print axioms Canary.erasure_not_sitePolicyCompatible
#print axioms Canary.no_sitePolicy_square_over_erasure
#print axioms Canary.active_eventCount_agrees
#print axioms Canary.relevant_change_prevents_activation

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionNIKAdmission
