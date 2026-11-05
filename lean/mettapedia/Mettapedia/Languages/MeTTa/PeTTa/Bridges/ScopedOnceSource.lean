import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedGuardSource

/-! Complete literal first-witness execution in the captured-query profile.
The raw operands and reached frame are retained at query entry. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Guards

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination

theorem literal_first_prefix {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (inside kept : List (CollectionWork Context)) (previousBoundary : Nat)
    (space pattern destination : Atom) (request : LiteralQuerySource.Request) (rows : List Atom)
    (environment afterEnvironment : Environment) (bindings : Equations)
    (frontier : scope.frontier = (control, context, origins) :: inside ++ kept)
    (atCall : control.goals = [.invoke "match" [space, pattern, request.payload] destination,
      .commit, .restoreCommit previousBoundary])
    (boundary : control.cutBoundary = kept.length) (resolved : resolve control.bindings = some environment)
    (location : read environment space = Effects.handleValue request.handle)
    (reading : read environment pattern = request.pattern) (snapshot : world.state.read request.handle = some rows)
    (ready : ClosedQueryAdmission.rowsReady request.pattern rows = true) (present : request.pattern ∈ rows)
    (refined : refine control.bindings request.payload destination = some bindings)
    (afterResolved : resolve bindings = some afterEnvironment) :
    let answer : CollectedAnswer := ⟨read afterEnvironment control.destination, bindings, origins ++ [0], []⟩
    let after : ScopedCursor Context := (allocator, ⟨world, EagerDFS.Scope.record scope kept answer :: parents⟩)
    (machine policy program).run 5 (allocator, ⟨world, scope :: parents⟩) =
      (if scope.caller.isNone then [answer] else [], .exhausted after) := by
  obtain ⟨values, first⟩ : ∃ values, SpaceSemantics.query rows request.pattern request.payload = request.payload :: values := by
    cases found : FirstQueryCursor.reference [] request.pattern (0, rows) with
    | none => exact False.elim (((LiteralQuerySource.reference_absent request rows).mp found) present)
    | some entry =>
        exact ConstantQuerySource.cursor_hit_has_first_answer request.pattern request.payload request.scalar rows
          (rows.length + 1) entry (by rw [FirstQueryCursor.complete, found])
  let older : List Goal := [.commit, .restoreCommit previousBoundary]
  let firstControl : Control := {control with goals := .equate request.payload destination :: older}
  let accepted : Control := {control with bindings, goals := older}
  let younger := OncePrimitiveSource.laterWork control context origins destination older values ++ inside
  let scope₁ : CollectionScope Context :=
    {scope with frontier := (firstControl, context, origins ++ [0]) :: younger ++ kept}
  let scope₂ : CollectionScope Context :=
    {scope with frontier := (accepted, context, origins ++ [0]) :: younger ++ kept}
  have firstStep : (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, scope₁ :: parents⟩)) := by
    rw [Caller.literal_query_step policy program allocator world scope parents control context origins (inside ++ kept)
      space pattern destination older environment request rows frontier atCall resolved location reading snapshot ready]
    have actual := scope_primitive_success policy program allocator world scope parents control context origins
      (inside ++ kept) "match" [space, pattern, request.payload] destination older environment world.state
      (request.payload :: values) frontier atCall resolved (by decide) (by decide)
      (by simp only [List.map_cons, List.map_nil, location, reading, LiteralQuerySource.read_payload]
          rw [ConstantQuerySource.primitive_query world.state request.handle rows request.pattern request.payload snapshot, first])
    simpa [OncePrimitiveSource.primitive_cons, scope₁, firstControl, younger, List.append_assoc] using congrArg some actual
  have secondStep : (machine policy program).step (allocator, ⟨world, scope₁ :: parents⟩) =
      some (.silent (allocator, ⟨world, scope₂ :: parents⟩)) := by
    rw [ordinary_step policy program allocator world scope₁ parents firstControl context (origins ++ [0])
      (younger ++ kept) (.equate request.payload destination) older rfl rfl rfl]
    simp [scopeStep, scope₁, scope₂, firstControl, accepted, older, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, refined, installChild, retainChild]
  rw [Machine.run_succ_silent _ firstStep, Machine.run_succ_silent _ secondStep]
  have committed := commit_first_answer policy program allocator world scope₂ parents accepted context (origins ++ [0])
    younger kept previousBoundary afterEnvironment rfl rfl boundary afterResolved
  simpa [scope₂, accepted, EagerDFS.Scope.record] using committed

open ClosedOnceQueryFrame
open LiteralQuerySource (Request query expression read_pattern read_payload read_handle)

set_option maxHeartbeats 1200000 in
theorem framed_entry {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings) :
    (machine .relational program).run 5
      (placed allocator world scope parents (initial frame request) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (ready frame request pending.length) context origins pending)) := by
  have refined := location_refined frame request pending.length consistent
  simp only [ready, location, calling, initial, query] at refined
  cases handle : request.handle <;> simp only [handle, Effects.handleValue] at refined ⊢ <;>
    simp [Machine.run, machine, step, syntaxStep, constrainedCall, mutationCall, queryStep,
      placed, initial, expression, query, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, callable,
      StdLib.known, Eval.ioHead, callArguments, freshSlots, List.range_succ, Eval.argumentIsRaw,
      StdLib.rawArgument, ready, location, calling, handle, Effects.handleValue, refined]

theorem framed_hit {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (fresh : FreshFor frame.output frame.bindings) (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) (present : request.pattern ∈ rows) :
    (machine .relational program).run 5
      (placed allocator world scope parents (ready frame request pending.length) context origins pending) =
      (if scope.caller.isNone then [answer frame request pending.length origins] else [],
        .exhausted (allocator, ⟨world, EagerDFS.Scope.record scope pending
          (answer frame request pending.length origins) :: parents⟩)) := by
  obtain ⟨environment, resolved⟩ := resolve_complete (ready_consistent frame request pending.length consistent)
  have refined := answer_refined frame request pending.length consistent fresh
  obtain ⟨afterEnvironment, afterResolved⟩ := resolve_complete (refined_consistent _ _ _ refined)
  have operands := ready_operands frame request pending.length environment resolved
  have locationRead := (List.cons.inj operands).1
  have actual := literal_first_prefix .relational program allocator world
    {scope with frontier := (ready frame request pending.length, context, origins) :: pending} parents
    (ready frame request pending.length) context origins [] pending frame.boundary
    (.var (location frame request pending.length)) request.pattern (.var frame.output) request rows
    environment afterEnvironment (acceptedBindings frame request pending.length) rfl rfl rfl resolved
    locationRead (read_pattern request environment) snapshot closed present refined afterResolved
  simpa [placed, ready, calling, initial, answer, EagerDFS.Scope.record,
    answer_read frame request pending.length afterEnvironment afterResolved] using actual

theorem framed_miss {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) (absent : request.pattern ∉ rows) :
    (machine .relational program).step
      (placed allocator world scope parents (ready frame request pending.length) context origins pending) =
      some (.silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  obtain ⟨environment, resolved⟩ := resolve_complete (ready_consistent frame request pending.length consistent)
  have operands := ready_operands frame request pending.length environment resolved
  exact Caller.literal_absence_step .relational program allocator world _ parents
    (ready frame request pending.length) context origins pending (.var (location frame request pending.length))
    request.pattern (.var frame.output) [.commit, .restoreCommit frame.boundary] environment request rows
    rfl rfl resolved (List.cons.inj operands).1 (read_pattern request environment) snapshot closed absent

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Guards
