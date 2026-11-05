import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryFrame

/-!
# Collected first-witness queries with their actual source caller

Literal collapse entry constructs the child frame from the complete retained
scope support. The child keeps inherited equations, and its first-witness
answer is collected rather than published outside the child. Returning to the
caller uses the existing generative allocator, including allocation refusal.
No intermediate copy identity, shared world or pending caller is discarded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request expression)
open ClosedOnceQueryFrame (Frame FreshFor)

def source (request : Request) : Atom :=
  .expression [.symbol "collapse", expression request]

def frame (control : Control) (boundary : Finset String) : Frame :=
  ⟨control.bindings, childName control boundary, control.support ∪ boundary, 0⟩

theorem frame_initial (control : Control) (boundary : Finset String)
    (request : Request) :
    ClosedOnceQueryFrame.initial (frame control boundary) request =
      collapseChild control boundary (expression request) := rfl

theorem frame_fresh (control : Control) (boundary : Finset String) :
    FreshFor (frame control boundary).output (frame control boundary).bindings := by
  apply ClosedOnceQueryFrame.fresh_for_bindings control
  intro member
  exact childName_fresh control boundary (Finset.mem_union_left _ member)

def caller {Context : Type} (control : Control) (destination : Atom) (older : List Goal)
    (context : Context) (origins : List Nat) : CollectionCaller Context :=
  ({control with goals := older}, destination, context, origins)

def entered {Context : Type} (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) : ScopedCursor Context :=
  (allocator, EagerDFS.Scope.enter world scope pending parents
    (collapseChild control (collectionSupport ⟨world, scope :: parents⟩)
      (expression request), context, origins)
    (caller control destination older context origins))

theorem entry_step {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (source request) destination :: older) :
    scopeStep .relational program (allocator, ⟨world, scope :: parents⟩) =
      .silent (entered allocator world scope parents control context origins pending destination older request) := by
  have entry := enterCollapse_constructs world scope parents control context origins pending
    (expression request) destination older frontier head
  simp only [scopeStep, frontier, entry, entered, caller]

def completed {Context : Type} (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) (present : Bool) : ScopedCursor Context :=
  (allocator, ⟨world,
    {frontier := [],
     collected := if present then [ClosedOnceQueryFrame.answer
       (frame control (collectionSupport ⟨world, scope :: parents⟩)) request 0 origins] else [],
     caller := some (caller control destination older context origins)} ::
    {scope with frontier := pending} :: parents⟩)

def childBudget (present : Bool) : Nat := if present then 10 else 6

theorem child_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request)
    (consistent : ∃ environment, Solves environment control.bindings) (rows : List Atom) (snapshot : world.state.read request.handle = some rows) :
    let present := decide (request.pattern ∈ rows)
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run (childBudget present)
      (entered allocator world scope parents control context origins pending destination older request) =
      ([], .exhausted (completed allocator world scope parents control context origins pending destination older request present)) := by
  let childFrame := frame control (collectionSupport ⟨world, scope :: parents⟩)
  let childScope : CollectionScope Context := {frontier := [], caller := some (caller control destination older context origins)}
  let parentScopes := {scope with frontier := pending} :: parents
  by_cases present : request.pattern ∈ rows
  · have actual := ClosedOnceQueryFrame.source_hit_prefix program allocator world childScope parentScopes
      childFrame context origins [] request consistent (frame_fresh _ _) rows snapshot present
    simpa [childBudget, present, entered, EagerDFS.Scope.enter, ClosedOnceQueryFrame.placed,
      completed, childScope, parentScopes, childFrame, frame_initial, EagerDFS.Scope.record] using actual
  · have actual := ClosedOnceQueryFrame.source_miss_prefix program allocator world childScope parentScopes
      childFrame context origins [] request consistent rows snapshot present
    simpa [childBudget, present, entered, EagerDFS.Scope.enter, ClosedOnceQueryFrame.placed,
      completed, childScope, parentScopes, childFrame, frame_initial] using actual

theorem source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (source request) destination :: older)
    (consistent : ∃ environment, Solves environment control.bindings) (rows : List Atom) (snapshot : world.state.read request.handle = some rows) :
    let present := decide (request.pattern ∈ rows)
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run (childBudget present + 1)
      (allocator, ⟨world, scope :: parents⟩) =
      ([], .exhausted (completed allocator world scope parents control context origins pending destination older request present)) := by
  dsimp only
  have step : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step
      (allocator, ⟨world, scope :: parents⟩) = some (.silent
        (entered allocator world scope parents control context origins pending destination older request)) := by
    rw [EagerDFSStreaming.Scoped.step_scope, entry_step program allocator world scope parents control context origins
      pending destination older request frontier head]
  rw [(EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run_succ_silent step]
  exact child_prefix program allocator world scope parents control context origins pending destination older
    request consistent rows snapshot

/-- Completing the child does not skip its generative return boundary. -/
theorem completed_step {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) (present : Bool) :
    let retained := completed allocator world scope parents control context origins pending destination older request present
    scopeStep .relational program retained =
      match finishAllocated? retained with
      | some next => .silent next
      | none => .call .allocation retained := by
  cases present <;> simp [scopeStep, completed, ClosedOnceQueryFrame.answer] <;> split <;> simp_all only

theorem source_return_boundary {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (source request) destination :: older)
    (consistent : ∃ environment, Solves environment control.bindings) (rows : List Atom) (snapshot : world.state.read request.handle = some rows) :
    let present := decide (request.pattern ∈ rows)
    let retained := completed allocator world scope parents control context origins pending destination older request present
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run (childBudget present + 2)
      (allocator, ⟨world, scope :: parents⟩) =
      ([], match finishAllocated? retained with
        | some next => .exhausted next
        | none => .suspended .allocation retained) := by
  dsimp only
  have reached := source_prefix program allocator world scope parents control context origins pending destination older
    request frontier head consistent rows snapshot
  have composed := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).established_and_pending
    (childBudget (decide (request.pattern ∈ rows)) + 1) 1 _ _ [] reached
  have step := completed_step program allocator world scope parents control context origins pending destination older
    request (decide (request.pattern ∈ rows))
  let retained := completed allocator world scope parents control context origins pending destination older
    request (decide (request.pattern ∈ rows))
  have actualStep : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step retained =
      some (match finishAllocated? retained with
        | some next => .silent next
        | none => .call .allocation retained) := by
    rw [EagerDFSStreaming.Scoped.step_scope]
    exact congrArg some step
  have one : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 1 retained =
      ([], match finishAllocated? retained with
        | some next => .exhausted next
        | none => .suspended .allocation retained) := by
    cases allocated : finishAllocated? retained with
    | none => simp only [allocated, Machine.run, actualStep]
    | some next => simp only [allocated, Machine.run, actualStep]
  rw [one] at composed
  simpa only [List.nil_append, Nat.add_assoc] using composed

/-- Once the actual copy boundary succeeds, every further source page is
the page of the retained caller. Fuel spent inside the child is not refunded. -/
theorem source_continuation {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) (next : ScopedCursor Context) (fuel : Nat)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (source request) destination :: older)
    (consistent : ∃ environment, Solves environment control.bindings) (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (allocated : finishAllocated? (completed allocator world scope parents control context origins pending destination older
      request (decide (request.pattern ∈ rows))) = some next) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run
        (childBudget (decide (request.pattern ∈ rows)) + 2 + fuel)
        (allocator, ⟨world, scope :: parents⟩) =
      (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run fuel next := by
  have returned := source_return_boundary program allocator world scope parents control context origins pending destination older
    request frontier head consistent rows snapshot
  dsimp only at returned
  rw [allocated] at returned
  have composed := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).established_and_pending
    (childBudget (decide (request.pattern ∈ rows)) + 2) fuel _ _ [] returned
  simpa only [List.nil_append] using composed

/-- The empty answer list allocates no copy identity, even when capacity is
zero. This differs from a collected singleton Boolean. -/
theorem empty_return {Context : Type}
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) :
    finishAllocated? (completed allocator world scope parents control context origins pending destination older request false) =
      some (allocator, ⟨world, {scope with frontier := (allocatedWork []
        (caller control destination older context origins) :: pending)} :: parents⟩) := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CollectedOnceQuerySource
