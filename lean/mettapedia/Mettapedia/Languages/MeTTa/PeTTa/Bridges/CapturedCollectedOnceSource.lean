import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPatternSupport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedPresenceSource

/-!
# Captured queries rejoin the existing collection boundary

The child runs the authored raw pattern. Its principal closed reading and
retained equations make its completed answer identical to the existing
literal-frame packet. The common endpoint precedes copying, so successful
copying and allocation refusal reuse the same source state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedCollectedOnceSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request)
open ClosedOnceQueryFrame (placed)
open CollectedOnceQuerySource (frame caller completed childBudget)

def source (request : Request) (patternCode : Atom) : Atom :=
  .expression [.symbol "collapse", CapturedOnceSource.source request patternCode]

def entered {Context : Type} (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) (patternCode : Atom) : ScopedCursor Context :=
  (allocator, EagerDFS.Scope.enter world scope pending parents
    (collapseChild control (collectionSupport ⟨world, scope :: parents⟩)
      (CapturedOnceSource.source request patternCode), context, origins)
    (caller control destination older context origins))

theorem child_rejoins {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) (patternCode : Atom) (principal : Environment)
    (resolved : resolve control.bindings = some principal) (reading : read principal patternCode = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    (ScopedQuerySource.machine .relational program).run (childBudget present)
      (entered allocator world scope parents control context origins pending destination older request patternCode) =
      ([], .exhausted (completed allocator world scope parents control context origins pending destination older request present)) := by
  let childFrame := frame control (collectionSupport ⟨world, scope :: parents⟩)
  let childScope : CollectionScope Context := {frontier := [], caller := some (caller control destination older context origins)}
  let parents' := {scope with frontier := pending} :: parents
  have actual := CapturedOnceSource.source_prefix program allocator world childScope parents' childFrame context origins []
    request patternCode principal resolved reading (CollectedOnceQuerySource.frame_fresh _ _) rows snapshot closed
  have same := CapturedPatternSupport.answer_eq_literal childFrame request patternCode 0 origins principal resolved reading
  dsimp only at actual
  simp only [List.length_nil, same] at actual
  by_cases present : request.pattern ∈ rows <;>
    simpa [childBudget, present, entered, EagerDFS.Scope.enter, placed, completed, childScope, parents',
      childFrame, frame, CapturedOnceSource.initial, collapseChild, EagerDFS.Scope.record] using actual

theorem source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) (patternCode : Atom) (principal : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (source request patternCode) destination :: older)
    (resolved : resolve control.bindings = some principal) (reading : read principal patternCode = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    (ScopedQuerySource.machine .relational program).run (childBudget present + 1) (allocator, ⟨world, scope :: parents⟩) =
      ([], .exhausted (completed allocator world scope parents control context origins pending destination older request present)) := by
  dsimp only
  have entry : (ScopedQuerySource.machine .relational program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (entered allocator world scope parents control context origins pending destination older request patternCode)) := by
    rw [ScopedQuerySource.Guards.ordinary_step .relational program allocator world scope parents control context origins pending
      (.evaluate (source request patternCode) destination) older frontier head rfl]
    have constructed := enterCollapse_constructs world scope parents control context origins pending
      (CapturedOnceSource.source request patternCode) destination older frontier head
    simp only [scopeStep, frontier, constructed, entered, caller]
  rw [Machine.run_succ_silent _ entry]
  exact child_rejoins program allocator world scope parents control context origins pending destination older request patternCode
    principal resolved reading rows snapshot closed

/-- Both successful copying and allocation suspension are the existing common
boundary; no second interpretation of the captured pattern is required. -/
theorem source_return_boundary {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) (patternCode : Atom) (principal : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (source request patternCode) destination :: older)
    (resolved : resolve control.bindings = some principal) (reading : read principal patternCode = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    let retained := completed allocator world scope parents control context origins pending destination older request present
    (ScopedQuerySource.machine .relational program).run (childBudget present + 2) (allocator, ⟨world, scope :: parents⟩) =
      ([], match finishAllocated? retained with
        | some next => .exhausted next
        | none => .suspended .allocation retained) := by
  dsimp only
  have reached := source_prefix program allocator world scope parents control context origins pending destination older request
    patternCode principal frontier head resolved reading rows snapshot closed
  have composed := (ScopedQuerySource.machine .relational program).established_and_pending
    (childBudget (decide (request.pattern ∈ rows)) + 1) 1 _ _ [] reached
  let retained := completed allocator world scope parents control context origins pending destination older request
    (decide (request.pattern ∈ rows))
  have actual : (ScopedQuerySource.machine .relational program).step retained =
      some (match finishAllocated? retained with
        | some next => .silent next
        | none => .call .allocation retained) := by
    have same : (ScopedQuerySource.machine .relational program).step retained = some (scopeStep .relational program retained) :=
      ScopedQuerySource.Guards.empty_frontier_step .relational program allocator world _ _ rfl
    rw [same]
    exact congrArg some (CollectedOnceQuerySource.completed_step program allocator world scope parents control context origins pending
      destination older request (decide (request.pattern ∈ rows)))
  have one : (ScopedQuerySource.machine .relational program).run 1 retained =
      ([], match finishAllocated? retained with
        | some next => .exhausted next
        | none => .suspended .allocation retained) := by
    cases allocated : finishAllocated? retained <;> simp only [Machine.run, actual, allocated]
  rw [one] at composed
  simpa only [List.nil_append, Nat.add_assoc] using composed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedCollectedOnceSource
