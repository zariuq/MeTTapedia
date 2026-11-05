import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryOperands
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# Exact prepared once-query pages from captured operands

The classifier reads the actual pending invocation, reached equations and
choice boundary. Its worker probes the captured complete domain and preserves
the original source control. A witness follows the proved five-inspection
commit prefix. A complete miss removes one branch and runs the remaining four
source inspections, preserving any caller work and effects in that page.

Probe exhaustion, unsupported operands or rows, invalid delimiters and a
refused result refinement decline at the exact entrance. No result is supplied
by a semantic oracle. Capturing/validating the domain is not charged by the
probe budget, and this is not a native performance or concurrent-use theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceQueryRegion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Dynamics ObservationQualified PartialRegionPlan
open EagerDFS (World)
open EagerDFS.Destination
open CapturedQueryOperands (Arguments Captured)

abbrev Result (Context : Type) :=
  List CollectedAnswer × Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary

structure Return (before : Equations) (value destination : Atom) where
  bindings : Equations
  environment : Environment
  refined : refine before value destination = some bindings
  resolved : resolve bindings = some environment

def prepareReturn (before : Equations) (value destination : Atom) : Option (Return before value destination) :=
  match refined : refine before value destination with
  | none => none
  | some bindings =>
      match resolved : resolve bindings with
      | none => none
      | some environment => some ⟨bindings, environment, refined, resolved⟩

private theorem no_events (events : List Empty) : events = [] := by
  cases events with
  | nil => rfl
  | cons impossible _ => exact nomatch impossible

def atInvocation {Context : Type} (program : SpaceSemantics.Program) (probeBudget : Nat)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (arguments : Arguments)
    (destination : Atom) (previousBoundary : Nat)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (goals : control.goals = [.invoke "match" arguments.atoms destination, .commit, .restoreCommit previousBoundary])
    (bounded : control.cutBoundary ≤ pending.length) :
    Option { result : Result Context //
      (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 5
        (allocator, ⟨world, scope :: parents⟩) = result } := do
  let captured ← CapturedQueryOperands.capture control.bindings arguments
  let reading ← LiteralQuerySource.prepareRead captured.request world.state
  match completed : ((FirstQueryCursor.machine [] captured.request.pattern).run probeBudget (0, reading.rows)).2 with
  | .finished witness =>
      have full : (FirstQueryCursor.machine [] captured.request.pattern).run probeBudget (0, reading.rows) =
          ([], .finished witness) := Prod.ext (no_events _) completed
      match found : witness with
      | none =>
          let after : ScopedCursor Context := (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)
          have sourceStep := ConstantQuerySource.empty_query_keeps_outer_work .relational program allocator world scope parents
            control context origins pending arguments.atoms destination captured.request.pattern captured.request.payload
            [.commit, .restoreCommit previousBoundary] captured.request.handle reading.rows probeBudget
            captured.principal frontier goals captured.resolved captured.operands reading.snapshot
            (by simpa only [found] using full)
          have step : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step
              (allocator, ⟨world, scope :: parents⟩) = some (.silent after) := by
            rw [EagerDFSStreaming.Scoped.step_scope, sourceStep]
          pure ⟨(EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 4 after,
            by rw [Machine.run_succ_silent _ step]⟩
      | some entry =>
          let returned ← prepareReturn control.bindings captured.request.payload destination
          let inside := pending.take (pending.length - control.cutBoundary)
          let kept := pending.drop (pending.length - control.cutBoundary)
          let answer : CollectedAnswer :=
            ⟨EagerDFS.Destination.read returned.environment control.destination, returned.bindings, origins ++ [0], []⟩
          let after : ScopedCursor Context :=
            (allocator, ⟨world, EagerDFS.Scope.record scope kept answer :: parents⟩)
          have splitFrontier : scope.frontier = (control, context, origins) :: inside ++ kept := by
            simpa [inside, kept, List.take_append_drop] using frontier
          have boundary : control.cutBoundary = kept.length := by
            simp only [kept, List.length_drop]
            omega
          have source := ConstantQuerySource.first_query_prefix .relational program allocator world scope parents
            control context origins inside kept previousBoundary arguments.atoms destination captured.request.pattern
            captured.request.payload captured.request.scalar captured.request.handle reading.rows probeBudget entry
            captured.principal returned.environment returned.bindings splitFrontier goals boundary captured.resolved
            captured.operands reading.snapshot (by simpa only [found] using full) returned.refined returned.resolved
          pure ⟨(if scope.caller.isNone then [answer] else [], .exhausted after), source⟩
  | _ => none

/-- Structural selection of an actual pending source occurrence. No change
is made while checking the source shape or the saved choice boundary. -/
def checked {Context : Type} (program : SpaceSemantics.Program) (probeBudget : Nat)
    (source : ScopedCursor Context) : Option { result : Result Context //
      (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 5 source = result } :=
  match source with
  | (allocator, ⟨world, scope :: parents⟩) =>
      match frontier : scope.frontier with
      | (control, context, origins) :: pending =>
          match goals : control.goals with
          | [.invoke "match" [location, pattern, payload] destination, .commit, .restoreCommit previousBoundary] =>
              if bounded : control.cutBoundary ≤ pending.length then
                atInvocation program probeBudget allocator world scope parents control context origins pending
                  ⟨location, pattern, payload⟩ destination previousBoundary frontier goals bounded
              else none
          | _ => none
      | [] => none
  | _ => none

def boundary (Context : Type) (program : SpaceSemantics.Program) :
    Boundary (ScopedCursor Context) (Result Context) (Result Context) where
  source := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 5
  summarize := id
  future := {Question := Unit, Answer _ := Result Context, read _ result := result}
  sufficient _ _ same _ := same

def region {Context Regime : Type} (regime : Regime) (program : SpaceSemantics.Program) (probeBudget : Nat) :
    CertifiedRegion (boundary Context program) Regime where
  regime := regime
  Artifact := Result Context
  attempt source := match checked program probeBudget source with
    | none => .declined source
    | some result => .committed result.val
  decode := id
  restores source restored declined := by
    dsimp only at declined
    split at declined
    · exact (Attempt.declined.inj declined).symm
    · cases declined
  exact source output committed := by
    split at committed
    · cases committed
    · rename_i result selected
      cases Attempt.committed.inj committed
      exact result.property.symm

theorem execute_exact {Context Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (probeBudget : Nat) (source : ScopedCursor Context) :
    (region regime program probeBudget).execute source =
      (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 5 source :=
  congrFun (CertifiedRegion.execute_eq_reference (region regime program probeBudget)) source

theorem continuation_exact {Context Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (probeBudget : Nat) (source : ScopedCursor Context) {Answer : Type}
    (continuation : Result Context → Answer) :
    continuation ((region regime program probeBudget).execute source) =
      continuation ((EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 5 source) := by
  rw [execute_exact]

theorem refused_entrance {Context Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (probeBudget : Nat) (source : ScopedCursor Context)
    (refused : checked program probeBudget source = none) :
    (region regime program probeBudget).attempt source = .declined source := by
  simp only [region, refused]

theorem refused_observation_entrance {Context Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (probeBudget : Nat) (source : ScopedCursor Context)
    (refused : checked program probeBudget source = none) :
    (region regime program probeBudget).observationAttempt source = .declined source := by
  simp only [CertifiedRegion.observationAttempt, refused_entrance regime program probeBudget source refused]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceQueryRegion
