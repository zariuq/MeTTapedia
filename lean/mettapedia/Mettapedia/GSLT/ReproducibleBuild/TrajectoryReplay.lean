import Mettapedia.GSLT.Core.ReproducibleBuild
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Basic

/-!
# Source-scoped trajectory replay

Hatta's fifth AGI-oriented reproducible-build requirement asks an evolving
system to retain the full ordered trajectory of checkpoints, code changes, and
self-produced or curated data.  A final state alone is not that trajectory.

This file separates an authoritative, proof-relevant transition relation from
an executable replay function.  Replay agrees with current-state
reconstruction only when the log fixes the initial state, covers the same
events, retains their required source scopes, respects an injective event
ordering, implements the authoritative transition relation exactly, and is
current at the requested revision.  The equivalence is a MeTTapedia extension
of Hatta's R5 requirement, not a claim made in Hatta (2026).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

universe uState uEvent uSource uRevision uKey

/-! ## Authoritative transitions and executable replay -/

/-- A transition system keeps the authoritative, proof-relevant step relation
distinct from the executable step used to replay a log. -/
structure EventSystem (State : Type uState) (Event : Type uEvent) where
  Step : State -> Event -> State -> Type (max uState uEvent)
  step? : State -> Event -> Option State

/-- The executable step implements exactly the possible target states of the
authoritative transition relation.  Multiple witnesses for one target state
remain possible. -/
def TransitionAdequate {State : Type uState} {Event : Type uEvent}
    (system : EventSystem State Event) : Prop :=
  forall initial event final,
    system.step? initial event = some final <->
      Nonempty (system.Step initial event final)

/-- A proof-relevant trajectory retains every intermediate transition witness
instead of reducing a run to its endpoint. -/
inductive Trajectory {State : Type uState} {Event : Type uEvent}
    (Step : State -> Event -> State -> Type (max uState uEvent)) :
    State -> List Event -> State -> Type (max uState uEvent) where
  | nil (state : State) : Trajectory Step state [] state
  | cons {initial middle final : State} {event : Event} {events : List Event}
      (head : Step initial event middle)
      (tail : Trajectory Step middle events final) :
      Trajectory Step initial (event :: events) final

/-- Execute an ordered event stream from an initial state. -/
def replay {State : Type uState} {Event : Type uEvent}
    (system : EventSystem State Event) : State -> List Event -> Option State
  | initial, [] => some initial
  | initial, event :: events => do
      let middle <- system.step? initial event
      replay system middle events

/-- Transition adequacy is exactly the premise needed to recover a
proof-relevant authoritative trajectory from successful executable replay and
conversely. -/
theorem replay_eq_some_iff_trajectory
    {State : Type uState} {Event : Type uEvent}
    (system : EventSystem State Event)
    (adequate : TransitionAdequate system) :
    forall (initial : State) (events : List Event) (final : State),
      replay system initial events = some final <->
        Nonempty (Trajectory system.Step initial events final) := by
  intro initial events
  induction events generalizing initial with
  | nil =>
      intro final
      constructor
      · intro replayed
        simp [replay] at replayed
        subst final
        exact ⟨Trajectory.nil initial⟩
      · rintro ⟨trajectory⟩
        cases trajectory
        rfl
  | cons event events ih =>
      intro final
      constructor
      · intro replayed
        simp only [replay] at replayed
        cases stepResult : system.step? initial event with
        | none => simp [stepResult] at replayed
        | some middle =>
            have tailReplay : replay system middle events = some final := by
              simpa [stepResult] using replayed
            obtain ⟨head⟩ := (adequate initial event middle).mp stepResult
            obtain ⟨tail⟩ := (ih middle final).mp tailReplay
            exact ⟨Trajectory.cons head tail⟩
      · rintro ⟨trajectory⟩
        cases trajectory with
        | cons head tail =>
            have headReplay := (adequate _ _ _).mpr ⟨head⟩
            have tailReplay := (ih _ _).mpr ⟨tail⟩
            simp [replay, headReplay, tailReplay]

/-! ## Source-scoped logs and their ordering -/

/-- One retained event together with the evidence sources on which it depends.
The source scope is not inferred from the event payload. -/
structure SourceScopedEvent (Event : Type uEvent) (Source : Type uSource) where
  event : Event
  sources : Finset Source

/-- A replayable log records its initial state, ordered event occurrences, and
the revision at which that record was issued. -/
structure EventLog (State : Type uState) (Event : Type uEvent)
    (Source : Type uSource) (Revision : Type uRevision) where
  initial : State
  records : List (SourceScopedEvent Event Source)
  issuedAt : Revision

namespace EventLog

variable {State : Type uState} {Event : Type uEvent}
  {Source : Type uSource} {Revision : Type uRevision}

/-- The ordered event payloads retained by a log. -/
def events (log : EventLog State Event Source Revision) : List Event :=
  log.records.map SourceScopedEvent.event

/-- Every recorded event retains all sources required by the declared
source-dependency discipline. -/
def SourceComplete [DecidableEq Source]
    (log : EventLog State Event Source Revision)
    (requiredSources : Event -> Finset Source) : Prop :=
  forall record, record ∈ log.records ->
    requiredSources record.event ⊆ record.sources

/-- Revision currentness is independent of successful replay and source
completeness. -/
def CurrentAt (log : EventLog State Event Source Revision)
    (currentRevision : Revision) : Prop :=
  log.issuedAt = currentRevision

end EventLog

/-- An injective key makes the event ordering explicit and lets completeness
as a multiset plus ordering recover the exact event list. -/
structure EventOrder (Event : Type uEvent) where
  Key : Type uKey
  linearOrder : LinearOrder Key
  key : Event -> Key
  injective : Function.Injective key

namespace EventOrder

/-- Events respect an ordering discipline when their injective keys are
nondecreasing. -/
def Valid {Event : Type uEvent} (order : EventOrder.{uEvent, uKey} Event)
    (events : List Event) : Prop :=
  letI := order.linearOrder
  (events.map order.key).Pairwise (· <= ·)

/-- Complete event coverage alone supplies only a permutation.  If both the
authoritative and retained streams satisfy the same injective ordering, their
ordered lists are equal. -/
theorem eq_of_perm_of_valid
    {Event : Type uEvent} (order : EventOrder.{uEvent, uKey} Event)
    {left right : List Event} (permuted : left.Perm right)
    (leftValid : order.Valid left) (rightValid : order.Valid right) :
    left = right := by
  letI := order.linearOrder
  have keyPerm : (left.map order.key).Perm (right.map order.key) :=
    permuted.map order.key
  have keyEq : left.map order.key = right.map order.key :=
    List.Perm.eq_of_pairwise' leftValid rightValid keyPerm
  exact (List.map_injective_iff.mpr order.injective) keyEq

end EventOrder

/-! ## The reconstruction theorem -/

/-- The explicit premises under which a source-scoped event log may stand for
an authoritative trajectory.  Event coverage retains multiplicity through
`List.Perm`; source completeness, ordering, transition adequacy, and
currentness are independent fields. -/
structure ReplayPremises
    {State : Type uState} {Event : Type uEvent} {Source : Type uSource}
    {Revision : Type uRevision} [DecidableEq Source]
    (system : EventSystem State Event)
    (order : EventOrder.{uEvent, uKey} Event)
    (requiredSources : Event -> Finset Source)
    (authoritativeInitial : State) (authoritativeEvents : List Event)
    (log : EventLog State Event Source Revision)
    (currentRevision : Revision) : Prop where
  initialState : log.initial = authoritativeInitial
  eventCoverage : log.events.Perm authoritativeEvents
  authoritativeOrder : order.Valid authoritativeEvents
  recordedOrder : order.Valid log.events
  sourceComplete : log.SourceComplete requiredSources
  transitionAdequate : TransitionAdequate system
  current : log.CurrentAt currentRevision

/-- Under the complete R5 premises, proof-relevant current-state
reconstruction is equivalent to executable log replay.  Neither side is
defined in terms of the other. -/
theorem currentStateReconstruction_iff_logReplay
    {State : Type uState} {Event : Type uEvent} {Source : Type uSource}
    {Revision : Type uRevision} [DecidableEq Source]
    (system : EventSystem State Event)
    (order : EventOrder.{uEvent, uKey} Event)
    (requiredSources : Event -> Finset Source)
    (authoritativeInitial : State) (authoritativeEvents : List Event)
    (log : EventLog State Event Source Revision)
    (currentRevision : Revision)
    (premises : ReplayPremises system order requiredSources
      authoritativeInitial authoritativeEvents log currentRevision)
    (final : State) :
    Nonempty (Trajectory system.Step authoritativeInitial
      authoritativeEvents final) <->
      replay system log.initial log.events = some final := by
  have eventsEq : log.events = authoritativeEvents :=
    order.eq_of_perm_of_valid premises.eventCoverage
      premises.recordedOrder premises.authoritativeOrder
  rw [premises.initialState, eventsEq]
  exact (replay_eq_some_iff_trajectory system
    premises.transitionAdequate authoritativeInitial authoritativeEvents final).symm

/-! ## Controls: omission and reordering are observable -/

namespace Canary

inductive Update where
  | reset
  | increment
deriving DecidableEq, Repr

def updateSystem : EventSystem Nat Update where
  Step := fun initial event final =>
    match event with
    | .reset => PLift (final = 0)
    | .increment => PLift (final = initial + 1)
  step? := fun initial event =>
    match event with
    | .reset => some 0
    | .increment => some (initial + 1)

theorem updateSystem_transitionAdequate :
    TransitionAdequate updateSystem := by
  intro initial event final
  cases event <;> simp [updateSystem, eq_comm]

def updateOrder : EventOrder Update where
  Key := Nat
  linearOrder := inferInstance
  key
    | .reset => 0
    | .increment => 1
  injective := by
    intro left right equal
    cases left <;> cases right <;> simp_all

def requiredSources (_ : Update) : Finset Unit := {()}

def authoritativeEvents : List Update := [.reset, .increment]

def completeRecords : List (SourceScopedEvent Update Unit) :=
  [{ event := .reset, sources := {()} },
   { event := .increment, sources := {()} }]

def completeLog : EventLog Nat Update Unit Nat where
  initial := 41
  records := completeRecords
  issuedAt := 7

theorem completeLog_premises :
    ReplayPremises updateSystem updateOrder requiredSources 41
      authoritativeEvents completeLog 7 := by
  constructor
  · rfl
  · simp [EventLog.events, completeLog, completeRecords, authoritativeEvents]
  · change List.Pairwise (fun left right : Nat => left <= right) [0, 1]
    simp
  · change List.Pairwise (fun left right : Nat => left <= right) [0, 1]
    simp
  · intro record member
    simp [completeLog, completeRecords] at member
    rcases member with rfl | rfl <;> simp [requiredSources]
  · exact updateSystem_transitionAdequate
  · rfl

theorem authoritativeTrajectory :
    Nonempty (Trajectory updateSystem.Step 41 authoritativeEvents 1) := by
  refine ⟨Trajectory.cons (middle := 0) ?_
    (Trajectory.cons (middle := 1) ?_ (Trajectory.nil 1))⟩
  · exact ⟨rfl⟩
  · exact ⟨rfl⟩

theorem completeLog_reconstructs_current :
    replay updateSystem completeLog.initial completeLog.events = some 1 :=
  (currentStateReconstruction_iff_logReplay updateSystem updateOrder
    requiredSources 41 authoritativeEvents completeLog 7
    completeLog_premises 1).mp authoritativeTrajectory

/-- Dropping the second receipt loses the second transition and reconstructs
the wrong current state. -/
def lostReceiptLog : EventLog Nat Update Unit Nat where
  initial := 41
  records := [{ event := .reset, sources := {()} }]
  issuedAt := 7

theorem lostReceiptLog_does_not_reconstruct_current :
    replay updateSystem lostReceiptLog.initial lostReceiptLog.events != some 1 := by
  decide

theorem lostReceiptLog_not_eventComplete :
    Not (lostReceiptLog.events.Perm authoritativeEvents) := by
  intro permuted
  have lengths := permuted.length_eq
  simp [EventLog.events, lostReceiptLog, authoritativeEvents] at lengths

/-- The same event multiset in the wrong order reaches a different state.
Coverage therefore cannot replace the ordering premise. -/
def reorderedLog : EventLog Nat Update Unit Nat where
  initial := 41
  records :=
    [{ event := .increment, sources := {()} },
     { event := .reset, sources := {()} }]
  issuedAt := 7

theorem reorderedLog_has_complete_multiset :
    reorderedLog.events.Perm authoritativeEvents := by
  simpa [EventLog.events, reorderedLog, authoritativeEvents] using
    (List.Perm.swap Update.increment Update.reset []).symm

theorem reorderedLog_does_not_reconstruct_current :
    replay updateSystem reorderedLog.initial reorderedLog.events != some 1 := by
  decide

theorem reorderedLog_not_valid :
    Not (updateOrder.Valid reorderedLog.events) := by
  change Not (List.Pairwise (fun left right : Nat => left <= right) [1, 0])
  simp

/-- A semantically replayable record can nevertheless be stale. -/
def staleLog : EventLog Nat Update Unit Nat :=
  { completeLog with issuedAt := 6 }

theorem staleLog_not_current : Not (staleLog.CurrentAt 7) := by
  simp [EventLog.CurrentAt, staleLog, completeLog]

end Canary

end Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

#print axioms Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay.currentStateReconstruction_iff_logReplay
#print axioms Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay.Canary.completeLog_reconstructs_current
#print axioms Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay.Canary.reorderedLog_does_not_reconstruct_current
