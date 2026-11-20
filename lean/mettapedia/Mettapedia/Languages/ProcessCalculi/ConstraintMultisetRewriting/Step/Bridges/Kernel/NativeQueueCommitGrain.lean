import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsCorrespondence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsOpenMap
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness
import Mettapedia.GSLT.Core.OperationalRealization

/-!
# Independent commit grain at the interpreted native queue

The construction has an occurrence bag, a fixed set of schematic rules,
guards checked after the firing's tells, and one knowledge store. The
existing correspondence uses one match per firing. Here each actual pointed
event is proved to consume the queue's unique pending occurrence. Therefore
any pairwise independent family of such events has at most one member.

This is a property of one queue at one retained solution. It does not say
that independent rounds in other constructions have at most one match, or
identify synchronous, maximal, every-match or conflicting batches with an
independent round. No bulk successor, schedule or default is defined here.

A separate coarsening control groups exactly two successive queue events.
Its actual expansion is a path-valued realization of length two. It cannot
retain the ordinary zero-or-one-source-step readback while keeping the same
input-word observation. This dependent serial grouping is not a round of
independent matches.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeQueueCommitGrain

open InterpretedFrames NativeRecordRuns NativeRecordRunsCorrespondence
open MeTTaCalculus.OccurrenceCommits (Clash Independent)
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open FragmentsOfTheStep.TransitionMaps NativeRecordRunsOpenMap

universe u v

variable {Cell : NativeFieldSchema.Field → Type u} {Record : Type u} {Effect : Frame.{u}}
  {Index : Type v} {clauses : Index → QueueClause Cell Record Effect}

def selection {before after : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (event : PointedEvent clauses before after) : Selection Occurrence :=
  match event with
  | .fire _ actual _ _ _ => actual.selection

theorem takes_request {before after : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (event : PointedEvent clauses before after) :
    before.point.layout.request ∈ (selection event).taken := by
  cases event with
  | fire start actual admitted finish restriction =>
      have oldView := start.view
      rw [← restriction] at oldView
      obtain ⟨move⟩ := invert_move clauses _ actual admitted finish.environment finish.view.solved
        start.layout start.fields _ _ oldView
      change start.layout.request ∈ actual.selection.taken
      rw [move.input.taken]
      exact List.mem_cons_self

theorem clash {before firstLast secondLast : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (first : PointedEvent clauses before firstLast) (second : PointedEvent clauses before secondLast) :
    Clash ((selection first).commit (T := Unit)) ((selection second).commit (T := Unit)) := by
  apply Or.inl
  intro disjoint
  exact Finset.disjoint_left.mp disjoint (List.mem_toFinset.mpr (takes_request first))
    (List.mem_toFinset.mpr (takes_request second))

theorem not_independent {before firstLast secondLast : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (first : PointedEvent clauses before firstLast) (second : PointedEvent clauses before secondLast) :
    ¬ Independent (fun _ : Occurrence => ())
      ((selection first).commit (T := Unit)) ((selection second).commit (T := Unit)) :=
  fun independent => independent.1 (clash first second)

abbrev Outgoing (clauses : Index → QueueClause Cell Record Effect)
    (before : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)) :=
  Σ after, PointedEvent clauses before after

def Apart {before : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (first second : Outgoing clauses before) : Prop :=
  Independent (fun _ : Occurrence => ())
    ((selection first.2).commit (T := Unit)) ((selection second.2).commit (T := Unit))

theorem independent_length {before : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (events : List (Outgoing clauses before)) (independent : events.Pairwise Apart) :
    events.length ≤ 1 := by
  cases events with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second rest =>
          exact False.elim (not_independent first.2 second.2
            ((List.pairwise_cons.mp independent).1 second List.mem_cons_self))

theorem nonempty_independent_is_singleton {before : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (events : List (Outgoing clauses before)) (independent : events.Pairwise Apart)
    (nonempty : events ≠ []) : ∃ event, events = [event] := by
  have bounded := independent_length events independent
  cases events with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      cases rest with
      | nil => exact ⟨first,rfl⟩
      | cons second rest => simp only [List.length_cons] at bounded; omega

theorem singleton_independent {before : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (event : Outgoing clauses before) : ([event] : List (Outgoing clauses before)).Pairwise Apart :=
  List.pairwise_singleton Apart event

theorem two_occurrences_not_independent {before : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (first second : Outgoing clauses before) : ¬ [first,second].Pairwise Apart := by
  intro independent
  have bounded := independent_length [first,second] independent
  simp only [List.length_cons,List.length_nil] at bounded
  omega

/-- An explicit serial coarsening control; this is not a bulk commit. -/
def twoStepTheory (clauses : Index → QueueClause Cell Record Effect) : GSLT :=
  theoryOf (NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier))
    (fun first last => ∃ middle, (targetTheory clauses).Step first middle ∧
      (targetTheory clauses).Step middle last)

noncomputable def expandTwo (clauses : Index → QueueClause Cell Record Effect) :
    OperationalRealization (twoStepTheory clauses) (targetTheory clauses) where
  mapTerm := id
  mapEquiv := fun same => same
  mapStep := fun stepped => .cons ⟨(Classical.choose_spec stepped).1⟩
    (.cons ⟨(Classical.choose_spec stepped).2⟩ (.refl _))

theorem expandTwo_length (clauses : Index → QueueClause Cell Record Effect)
    {first last : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (stepped : (twoStepTheory clauses).Step first last) :
    ((expandTwo clauses).mapStep stepped).length = 2 := rfl

theorem two_steps_cannot_read_as_one {Observation : Type u}
    (read : ((name : NativeFieldSchema.Field) → Cell name) → Observation)
    (edge : Observation → (Record × Effect.Carrier) → Observation → Prop)
    {first middle last : NativeRecordRunsCorrespondence.Configuration Cell (Record × Effect.Carrier)}
    (firstStep : (targetTheory clauses).Step first middle)
    (lastStep : (targetTheory clauses).Step middle last) :
    ¬ ∃ reader : OperationalReadback (sourceTheory edge) (twoStepTheory clauses),
      ∀ source current, reader.related source current ↔ observe read current = source := by
  rintro ⟨reader,graph⟩
  have initial : reader.related (observe read first) first := (graph _ _).mpr rfl
  have stepped : (twoStepTheory clauses).Step first last := ⟨middle,firstStep,lastStep⟩
  have firstDrop := target_step_pending clauses firstStep
  have lastDrop := target_step_pending clauses lastStep
  rcases reader.readStep initial stepped with unchanged | ⟨after,sourceStep,related⟩
  · have same := congrArg (fun state => state.pending.length) ((graph _ _).mp unchanged)
    change last.pending.length = first.pending.length at same
    omega
  · have same := congrArg (fun state => state.pending.length) ((graph _ _).mp related)
    change last.pending.length = after.pending.length at same
    have sourceDrop := queue_step_pending sourceStep
    change after.pending.length + 1 = first.pending.length at sourceDrop
    omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeQueueCommitGrain
