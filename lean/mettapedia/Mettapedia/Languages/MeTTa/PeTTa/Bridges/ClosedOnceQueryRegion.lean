import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedQueryAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# An observation-qualified first-witness source region

The source is the actual scoped execution of a closed tagged once-query.
The alternative probes only until its first witness or its physical budget
ends. A paused probe refuses with the entrance intact; it never reports
absence. Full completed outcomes, including world and retained bindings,
are reconstructed without running the source evaluator in the worker.

Source-control fuel and row-probe budget are separate. Exact-page observers
are not admitted. The live closed-candidate check is conservative; no cost or
native unification claim follows from that semantic gate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryRegion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Dynamics ObservationQualified PartialRegionPlan
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryExecution

structure Input where
  allocator : Allocator
  world : World
  sourceFuel : Nat

abbrev Result := List CollectedAnswer × Outcome (ScopedCursor Unit) (ScopedCursor Unit) ScopeBoundary

def sourceBoundary (program : SpaceSemantics.Program) (source : Atom) :
    Boundary Input Result Result where
  source input := (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run input.sourceFuel
    (root input.allocator input.world
      {bindings := [], goals := [.evaluate source (.var "answer")], destination := .var "answer"})
  summarize := id
  future := {Question := Unit, Answer _ := Result, read _ result := result}
  sufficient _ _ same _ := same

def boundary (program : SpaceSemantics.Program) (relation : String) (formula node : Int) : Boundary Input Result Result :=
  sourceBoundary program (expression relation formula node)

def result (relation : String) (formula node : Int) (input : Input) (present : Bool) : Result :=
  (if present then [answer relation formula node] else [],
    .finished (completedState input.allocator input.world relation formula node present))

theorem source_result (program : SpaceSemantics.Program) (relation : String) (formula node : Int)
    (ordinary : relation ≠ "cons") (input : Input) (enough : 11 ≤ input.sourceFuel) :
    (boundary program relation formula node).reference input =
      result relation formula node input (decide (pattern relation formula node ∈ input.world.state.core)) := by
  have finished := source_finishes program input.allocator input.world relation formula node ordinary
  have stable := (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run_stable
    11 (input.sourceFuel - 11) (root input.allocator input.world (initialControl relation formula node))
    (fun residual => by rw [finished]; simp)
  have total : 11 + (input.sourceFuel - 11) = input.sourceFuel := by omega
  rw [total, finished] at stable
  simpa [boundary, sourceBoundary, Boundary.reference, initialControl, result] using stable

theorem reference_present (relation : String) (formula node : Int) (ordinary : relation ≠ "cons")
    (rows : List Atom) :
    (FirstQueryCursor.reference [] (pattern relation formula node) (0, rows)).isSome =
      decide (pattern relation formula node ∈ rows) := by
  cases found : FirstQueryCursor.reference [] (pattern relation formula node) (0, rows) with
  | none => simp [(reference_absent relation formula node rows ordinary).mp found]
  | some entry =>
      have present : pattern relation formula node ∈ rows := by
        by_contra absent
        have missing := (reference_absent relation formula node rows ordinary).mpr absent
        rw [found] at missing
        cases missing
      simp [present]

def attempt (relation : String) (formula node : Int) (probeBudget : Nat) (input : Input) : Attempt Input Result :=
  if 11 ≤ input.sourceFuel ∧ ClosedQueryAdmission.rowsReady (pattern relation formula node) input.world.state.core = true then
    match ((FirstQueryCursor.machine [] (pattern relation formula node)).run probeBudget (0, input.world.state.core)).2 with
    | .finished witness => .committed (result relation formula node input witness.isSome)
    | _ => .declined input
  else .declined input

private theorem no_events (events : List Empty) : events = [] := by
  cases events with
  | nil => rfl
  | cons impossible _ => exact nomatch impossible

theorem attempt_restores (relation : String) (formula node : Int) (probeBudget : Nat) :
    RestoresOnDecline (attempt relation formula node probeBudget) := by
  intro input restored declined
  unfold attempt at declined
  split at declined
  · split at declined
    · cases declined
    · exact (Attempt.declined.inj declined).symm
  · exact (Attempt.declined.inj declined).symm

theorem attempt_exact (program : SpaceSemantics.Program) (relation : String) (formula node : Int)
    (ordinary : relation ≠ "cons") (probeBudget : Nat) (input : Input) (output : Result)
    (accepted : attempt relation formula node probeBudget input = .committed output) :
    output = (boundary program relation formula node).reference input := by
  unfold attempt at accepted
  split at accepted
  next admitted =>
    split at accepted
    next witness completed =>
      have same : result relation formula node input witness.isSome = output := Attempt.committed.inj accepted
      subst output
      have full : (FirstQueryCursor.machine [] (pattern relation formula node)).run probeBudget
          (0, input.world.state.core) = ([], .finished witness) := Prod.ext (no_events _) completed
      have first := FirstQueryCursor.finished_exact [] (pattern relation formula node) probeBudget 0
        input.world.state.core witness full
      rw [first, reference_present relation formula node ordinary,
        source_result program relation formula node ordinary input admitted.1]
    next => cases accepted
  next => cases accepted

def region {Regime : Type} (regime : Regime) (program : SpaceSemantics.Program) (relation : String)
    (formula node : Int) (ordinary : relation ≠ "cons") (probeBudget : Nat) :
    CertifiedRegion (boundary program relation formula node) Regime where
  regime := regime
  Artifact := Result
  attempt := attempt relation formula node probeBudget
  decode := id
  restores := attempt_restores relation formula node probeBudget
  exact := attempt_exact program relation formula node ordinary probeBudget

def classify {Regime : Type} (regime : Regime) (observation : PureCallExtraction.Observation)
    (program : SpaceSemantics.Program) (relation : String) (formula node : Int)
    (ordinary : relation ≠ "cons") (probeBudget : Nat) :
    Option (CertifiedRegion (boundary program relation formula node) Regime) :=
  match observation with
  | .exactPage => none
  | .completedResult => some (region regime program relation formula node ordinary probeBudget)

theorem exact_page_declines {Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (relation : String) (formula node : Int) (ordinary : relation ≠ "cons") (probeBudget : Nat) :
    classify regime .exactPage program relation formula node ordinary probeBudget = none := rfl

theorem fallback_is_the_reference {Regime : Type} (regime : Regime) (program : SpaceSemantics.Program)
    (relation : String) (formula node : Int) (ordinary : relation ≠ "cons") (probeBudget : Nat) (input : Input) :
    (region regime program relation formula node ordinary probeBudget).execute input =
      (boundary program relation formula node).reference input := by
  exact congrFun (CertifiedRegion.execute_eq_reference _) input

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryRegion
