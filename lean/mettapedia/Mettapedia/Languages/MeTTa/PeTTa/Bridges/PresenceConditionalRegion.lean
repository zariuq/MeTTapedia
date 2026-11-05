import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryRegion

/-!
# First-witness realization of a source presence conditional

A bounded row cursor replaces the guard's collection and Boolean operations.
It reconstructs the exact reached source frame, including allocation and the
paid source-control prefix, then resumes the ordinary source machine. A
partial scan, unavailable domain or unavailable capacity declines without
publication. No physical cost bound follows from the source step accounting.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalRegion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Dynamics ObservationQualified PartialRegionPlan
open EagerDFS.Destination
open ClosedOnceQueryRegion (Input)
open ClosedOnceQueryFrame (placed)
open LiteralQuerySource (Request PreparedRead)

structure Frame (Context : Type) where
  scope : CollectionScope Context
  parents : List (CollectionScope Context)
  caller : Control
  context : Context
  origins : List Nat
  pending : List (CollectionWork Context)
  destination : Atom
  request : Request
  yes : Atom
  no : Atom
  consistent : ∃ environment, Solves environment caller.bindings

abbrev Result (Context : Type) :=
  List CollectedAnswer × Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary

def sourceSteps (present : Bool) : Nat := 1 + (CollectedOnceQuerySource.childBudget present + 10) + 2

def entrance {Context : Type} (frame : Frame Context) (input : Input) : ScopedCursor Context :=
  placed input.allocator input.world frame.scope frame.parents
    (PresenceConditionalSource.entry frame.caller frame.destination frame.request frame.yes frame.no)
    frame.context frame.origins frame.pending

def boundary {Context : Type} (program : SpaceSemantics.Program) (frame : Frame Context) :
    Boundary Input (Result Context) (Result Context) where
  source input := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run input.sourceFuel
    (entrance frame input)
  summarize := id
  future := {Question := Unit, Answer _ := Result Context, read _ result := result}
  sufficient _ _ same _ := same

def resume {Context : Type} (program : SpaceSemantics.Program) (frame : Frame Context)
    (input : Input) (allocator : Allocator) (present : Bool) : Result Context :=
  (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run (input.sourceFuel - sourceSteps present)
    (placed allocator input.world frame.scope frame.parents
      (PresenceConditionalSource.reached frame.caller frame.destination frame.request frame.yes frame.no present)
      frame.context (frame.origins ++ [0, 0]) frame.pending)

theorem source_resume {Context : Type} (program : SpaceSemantics.Program) (frame : Frame Context)
    (input : Input) (reading : PreparedRead frame.request input.world.state) (present : Bool) (allocator : Allocator)
    (truth : decide (frame.request.pattern ∈ reading.rows) = present)
    (enough : sourceSteps present ≤ input.sourceFuel)
    (allocated : PresenceGuardSource.copyAllocator input.allocator present = some allocator) :
    (boundary program frame).reference input = resume program frame input allocator present := by
  have guarded := PresenceConditionalSource.source_prefix program input.allocator input.world frame.scope frame.parents
    frame.caller frame.context frame.origins frame.pending frame.destination frame.request frame.yes frame.no
    frame.consistent reading.rows reading.snapshot
  dsimp only at guarded
  rw [truth, allocated] at guarded
  have continued := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).established_and_pending
    (sourceSteps present) (input.sourceFuel - sourceSteps present) _ _ [] guarded
  have total : sourceSteps present + (input.sourceFuel - sourceSteps present) = input.sourceFuel := Nat.add_sub_of_le enough
  rw [total] at continued
  simpa only [boundary, Boundary.reference, id_eq, resume, entrance, List.nil_append, Prod.mk.eta] using continued

theorem reference_present (request : Request) (rows : List Atom) :
    (FirstQueryCursor.reference [] request.pattern (0, rows)).isSome = decide (request.pattern ∈ rows) := by
  cases found : FirstQueryCursor.reference [] request.pattern (0, rows) with
  | none => simp [(LiteralQuerySource.reference_absent request rows).mp found]
  | some witness =>
      have present : request.pattern ∈ rows := by
        by_contra absent
        have missing := (LiteralQuerySource.reference_absent request rows).mpr absent
        rw [found] at missing
        cases missing
      simp [present]

def attempt {Context : Type} (program : SpaceSemantics.Program) (frame : Frame Context)
    (probeBudget : Nat) (input : Input) : Attempt Input (Result Context) :=
  match LiteralQuerySource.prepareRead frame.request input.world.state with
  | none => .declined input
  | some reading =>
      match ((FirstQueryCursor.machine [] frame.request.pattern).run probeBudget (0, reading.rows)).2 with
      | .finished witness =>
          if sourceSteps witness.isSome ≤ input.sourceFuel then
            match PresenceGuardSource.copyAllocator input.allocator witness.isSome with
            | none => .declined input
            | some allocator => .committed (resume program frame input allocator witness.isSome)
          else .declined input
      | _ => .declined input

theorem attempt_restores {Context : Type} (program : SpaceSemantics.Program) (frame : Frame Context)
    (probeBudget : Nat) : RestoresOnDecline (attempt program frame probeBudget) := by
  intro input restored declined
  unfold attempt at declined
  split at declined
  · exact (Attempt.declined.inj declined).symm
  · split at declined
    · split at declined
      · split at declined
        · exact (Attempt.declined.inj declined).symm
        · cases declined
      · exact (Attempt.declined.inj declined).symm
    · exact (Attempt.declined.inj declined).symm

private theorem no_events (events : List Empty) : events = [] := by
  cases events with
  | nil => rfl
  | cons impossible _ => exact nomatch impossible

theorem attempt_exact {Context : Type} (program : SpaceSemantics.Program) (frame : Frame Context)
    (probeBudget : Nat) (input : Input) (output : Result Context)
    (accepted : attempt program frame probeBudget input = .committed output) :
    output = (boundary program frame).reference input := by
  unfold attempt at accepted
  split at accepted
  · cases accepted
  next reading prepared =>
    split at accepted
    next witness completed =>
      split at accepted
      next enough =>
        split at accepted
        · cases accepted
        next allocator allocated =>
          cases Attempt.committed.inj accepted
          have runExact : (FirstQueryCursor.machine [] frame.request.pattern).run probeBudget (0, reading.rows) =
              ([], .finished witness) := Prod.ext (no_events _) completed
          have cursorExact := FirstQueryCursor.finished_exact [] frame.request.pattern probeBudget 0 reading.rows witness runExact
          have truth : decide (frame.request.pattern ∈ reading.rows) = witness.isSome := by
            rw [cursorExact, reference_present]
          exact (source_resume program frame input reading witness.isSome allocator truth enough allocated).symm
      next => cases accepted
    next => cases accepted

def region {Context Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (frame : Frame Context) (probeBudget : Nat) : CertifiedRegion (boundary program frame) Regime where
  regime := regime
  Artifact := Result Context
  attempt := attempt program frame probeBudget
  decode := id
  restores := attempt_restores program frame probeBudget
  exact := attempt_exact program frame probeBudget

theorem fallback_is_reference {Context Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (frame : Frame Context) (probeBudget : Nat) (input : Input) :
    (region regime program frame probeBudget).execute input = (boundary program frame).reference input :=
  congrFun (CertifiedRegion.execute_eq_reference _) input

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalRegion
