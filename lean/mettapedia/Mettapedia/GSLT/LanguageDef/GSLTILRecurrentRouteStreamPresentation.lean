import Mettapedia.GSLT.Core.SearchStreamProductivity
import Mettapedia.GSLT.LanguageDef.GSLTILRecurrentRouteBridge

/-!
# Stream presentation of retained recurrent GSLT-IL routes

Every controlled execution already determines a coherent cone of exact,
occurrence-retaining finite routes.  This module gives that cone one canonical
chronological stream presentation.  Node `index` emits the chosen realization
of the exact controlled occurrence at `index` and leaves `index + 1` live.

The presentation commutes with every retained route prefix: observing after
`depth` steps gives exactly the pointwise realization of that prefix's
occurrence list.  Consequently, every finite stream demand is met after the
same finite number of steps.

This construction uses local checked execution, not recurrence.  A
nonaccepting loop therefore has a productive occurrence stream while still
lacking Buechi recurrence.  The negative example prevents a stream interface
from laundering one liveness claim into another.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteStreamPresentation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.SearchControlProperties
open Mettapedia.GSLT.Core.SearchStreamProductivity
open Mettapedia.GSLT.Core.SearchStreamProductivity.Scenario
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteBridge

universe uView uMapped

variable {AuthorityId : Type} {theory : GSLT}
variable (stepAuthority : StepAuthority AuthorityId theory)
variable (claim : RecurrentTraceClaim theory stepAuthority.Certificate)

section Controlled

variable (execution : ControlledExecution claim.controller claim.root)
variable {View : Type uView}

/-- The realized answer at one exact controlled-execution index. -/
def realizedAt
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View)
    (index : Nat) : View :=
  realize (occurrenceAt stepAuthority claim execution index)

/-- The canonical one-live-node stream system of a controlled execution. -/
def streamSystem
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View) :
    BranchingSystem Nat View where
  emit index := some (realizedAt stepAuthority claim execution realize index)
  successors index := [index + 1]

/-- The canonical breadth-first stream presentation starts at epoch zero. -/
def streamScenario
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View) :
    Scenario Nat View where
  system := streamSystem stepAuthority claim execution realize
  scheduler := Scheduler.breadthFirst
  roots := [0]

/-- The controlled occurrence prefix is precisely natural-index enumeration. -/
theorem occurrencePrefix_eq_range_map (depth : Nat) :
    occurrencePrefix stepAuthority claim execution depth =
      (List.range depth).map
        (occurrenceAt stepAuthority claim execution) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [occurrencePrefix, inductionHypothesis, List.range_succ,
        List.map_append]
      rfl

/-- Exact finite snapshots retain both occurrence origin and realized value. -/
theorem stream_run_eq
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View)
    (fuel : Nat) :
    run (streamSystem stepAuthority claim execution realize)
        Scheduler.breadthFirst fuel (initial [0]) =
      { events := (List.range fuel).map
          (fun index =>
            ⟨index, realizedAt stepAuthority claim execution realize index⟩)
        frontier := [fuel] } := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      change
        tick (streamSystem stepAuthority claim execution realize)
            Scheduler.breadthFirst
            (run (streamSystem stepAuthority claim execution realize)
              Scheduler.breadthFirst fuel (initial [0])) =
          { events := (List.range (fuel + 1)).map
              (fun index =>
                ⟨index,
                  realizedAt stepAuthority claim execution realize index⟩)
            frontier := [fuel + 1] }
      rw [inductionHypothesis]
      simp [tick, Scheduler.breadthFirst, streamSystem, List.range_succ]
      rfl

theorem stream_frontier_eq_singleton
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View)
    (fuel : Nat) :
    ((streamScenario stepAuthority claim execution realize).snapshotAt fuel).frontier =
      [fuel] := by
  exact congrArg Snapshot.frontier
    (stream_run_eq stepAuthority claim execution realize fuel)

/-- The canonical occurrence stream remains open at every finite depth. -/
theorem stream_not_finitely_closes
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View) :
    ¬ (streamScenario stepAuthority claim execution realize).FinitelyCloses := by
  rintro ⟨fuel, closed⟩
  rw [Scenario.FrontierClosedAt,
    stream_frontier_eq_singleton stepAuthority claim execution realize] at closed
  simp at closed

/-- Observing the canonical stream gives exactly the pointwise realization of
the existing controlled occurrence prefix. -/
theorem observed_eq_realized_occurrencePrefix
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View)
    (depth : Nat) :
    EventObserver.value.observeList
        ((streamScenario stepAuthority claim execution realize).snapshotAt
          depth).events =
      (occurrencePrefix stepAuthority claim execution depth).map realize := by
  change
    EventObserver.value.observeList
        (run (streamSystem stepAuthority claim execution realize)
          Scheduler.breadthFirst depth (initial [0])).events =
      (occurrencePrefix stepAuthority claim execution depth).map realize
  rw [stream_run_eq, EventObserver.observeList_value,
    occurrencePrefix_eq_range_map]
  simp [realizedAt, List.map_map, Function.comp_def]

/-- Every finite pull of the authored realized occurrence stream is answered
after exactly the requested amount of fuel. -/
theorem stream_productive
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View) :
    StreamProductiveFor
      (streamScenario stepAuthority claim execution realize)
      EventObserver.value
      (realizedAt stepAuthority claim execution realize) := by
  intro demand
  refine ⟨demand, ?_⟩
  rw [streamPrefix_eq_range_map,
    observed_eq_realized_occurrencePrefix,
    occurrencePrefix_eq_range_map]
  unfold realizedAt
  rw [List.map_map]
  exact List.prefix_rfl

end Controlled

section Retained

variable [DecidableEq theory.Term]
variable (accepting : theory.Term → Bool)
variable (route : AuditedRecurrentExecution stepAuthority accepting claim)
variable {View : Type uView} {Mapped : Type uMapped}

/-- The stream square commutes with the occurrence list of every exact
path-retaining GSLT-IL prefix. -/
theorem observed_eq_realized_retainedPrefix
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View)
    (depth : Nat) :
    EventObserver.value.observeList
        ((streamScenario stepAuthority claim route.execution realize).snapshotAt
          depth).events =
      (AuditedRecurrentExecution.retainedPrefix stepAuthority accepting claim
        route depth).occurrences.map realize := by
  rw [observed_eq_realized_occurrencePrefix]
  rfl

/-- The retained route therefore has a productive chronological stream
presentation, independently of its separate recurrence field. -/
theorem retained_route_stream_productive
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View) :
    StreamProductiveFor
      (streamScenario stepAuthority claim route.execution realize)
      EventObserver.value
      (realizedAt stepAuthority claim route.execution realize) :=
  stream_productive stepAuthority claim route.execution realize

/-- Local post-observation maps preserve productivity without changing the
retained source route. -/
theorem retained_route_stream_productive_map
    (realize : ControlledOccurrence theory stepAuthority.Certificate → View)
    (mapView : View → Mapped) :
    StreamProductiveFor
      (streamScenario stepAuthority claim route.execution realize)
      (EventObserver.value.map mapView)
      (fun index =>
        mapView (realizedAt stepAuthority claim route.execution realize index)) :=
  (retained_route_stream_productive stepAuthority claim accepting route
    realize).map mapView

end Retained

/-! ## Negative control: productivity is not Buechi recurrence -/

namespace Canary

open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute.Canary
open Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteBridge.Canary

def nonacceptingStreamScenario :
    Scenario Nat
      (ControlledOccurrence loopTheory loopStepAuthority.Certificate) :=
  streamScenario loopStepAuthority loopClaim nonacceptingExecution id

/-- A locally checked nonaccepting loop supports arbitrary finite stream pulls
but still has no recurrent accepting visit. -/
theorem productive_stream_without_recurrence :
    StreamProductiveFor nonacceptingStreamScenario EventObserver.value
        (realizedAt loopStepAuthority loopClaim nonacceptingExecution id) ∧
      ¬ loopController.BuchiWinning
        (auditedLabeledSystem loopStepAuthority neverAccepting) loopClaim.root :=
  ⟨stream_productive loopStepAuthority loopClaim nonacceptingExecution id,
    nonaccepting_loop_not_recurrent⟩

end Canary

#print axioms occurrencePrefix_eq_range_map
#print axioms stream_run_eq
#print axioms stream_not_finitely_closes
#print axioms observed_eq_realized_occurrencePrefix
#print axioms stream_productive
#print axioms observed_eq_realized_retainedPrefix
#print axioms retained_route_stream_productive
#print axioms retained_route_stream_productive_map
#print axioms Canary.productive_stream_without_recurrence

end Mettapedia.GSLT.LanguageDef.GSLTIL.RecurrentRouteStreamPresentation
