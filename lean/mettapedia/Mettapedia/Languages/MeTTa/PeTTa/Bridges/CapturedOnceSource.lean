import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedOnceSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryOperands

/-!
# First-witness source entry with a captured pattern

The authored pattern remains in the source tree and in every prepared frame.
Its literal reading is obtained from the reached equations. Slot names are
allocated from the original code, not from a substituted literal expression.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request read_pattern read_payload read_handle)
open ClosedOnceQueryFrame (Frame FreshFor placed)

def query (request : Request) (patternCode : Atom) : Atom :=
  .expression [.symbol "match", Effects.handleValue request.handle, patternCode, request.payload]

def source (request : Request) (patternCode : Atom) : Atom :=
  .expression [.symbol "once", query request patternCode]

def initial (frame : Frame) (request : Request) (patternCode : Atom) : Control :=
  {bindings := frame.bindings, destination := .var frame.output, reserved := frame.reserved,
    cutBoundary := frame.boundary, goals := [.evaluate (source request patternCode) (.var frame.output)]}

def calling (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat) : Control :=
  {(initial frame request patternCode) with
    cutBoundary := kept,
    goals := [.evaluate (query request patternCode) (.var frame.output), .commit, .restoreCommit frame.boundary]}

def location (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat) : String :=
  freshName (calling frame request patternCode kept) 0

def ready (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat) : Control :=
  {(calling frame request patternCode kept) with
    bindings := frame.bindings ++ [(Effects.handleValue request.handle, .var (location frame request patternCode kept))],
    goals := [.invoke "match" [.var (location frame request patternCode kept), patternCode, request.payload]
      (.var frame.output), .commit, .restoreCommit frame.boundary]}

theorem principal_pattern_forces {bindings : Equations} {environment : Environment}
    (resolved : resolve bindings = some environment) (patternCode : Atom) (request : Request)
    (reading : read environment patternCode = request.pattern) :
    ∀ model, Solves model bindings → read model patternCode = request.pattern :=
  CapturedQueryOperands.resolved_forces resolved patternCode request.pattern reading (read_pattern request)

theorem location_fresh (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat) :
    FreshFor (location frame request patternCode kept) frame.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (calling frame request patternCode kept) _ (freshName_not_mem _ _)

theorem location_ne_output (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat) :
    location frame request patternCode kept ≠ frame.output := by
  intro equal
  have fresh := freshName_not_mem (calling frame request patternCode kept) 0
  apply fresh
  change location frame request patternCode kept ∈ _
  rw [equal]
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  exact Or.inr ⟨.var frame.output, by simp [calling, initial],
    by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

theorem location_refined (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat)
    (consistent : ∃ environment, Solves environment frame.bindings) :
    refine frame.bindings (Effects.handleValue request.handle) (.var (location frame request patternCode kept)) =
      some (ready frame request patternCode kept).bindings :=
  ClosedOnceQueryFrame.refine_fresh_closed _ _ _ (location_fresh frame request patternCode kept)
    consistent (read_handle request.handle)

theorem ready_consistent (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat)
    (consistent : ∃ environment, Solves environment frame.bindings) :
    ∃ environment, Solves environment (ready frame request patternCode kept).bindings :=
  ClosedOnceQueryFrame.refined_consistent _ _ _ (location_refined frame request patternCode kept consistent)

theorem ready_pattern (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat)
    (models : ∀ model, Solves model frame.bindings → read model patternCode = request.pattern)
    (environment : Environment) (resolved : resolve (ready frame request patternCode kept).bindings = some environment) :
    read environment patternCode = request.pattern := by
  apply models environment
  intro pair member
  exact resolve_sound resolved pair (List.mem_append_left _ member)

theorem ready_location (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat)
    (environment : Environment) (resolved : resolve (ready frame request patternCode kept).bindings = some environment) :
    read environment (.var (location frame request patternCode kept)) = Effects.handleValue request.handle := by
  have bound := resolve_sound resolved (Effects.handleValue request.handle, .var (location frame request patternCode kept))
    (List.mem_append_right _ (by simp))
  rw [read_handle] at bound
  exact bound.symm

set_option maxHeartbeats 1200000 in
theorem entry_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (request : Request) (patternCode : Atom)
    (consistent : ∃ environment, Solves environment frame.bindings) :
    (ScopedQuerySource.machine .relational program).run 5
      (placed allocator world scope parents (initial frame request patternCode) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (ready frame request patternCode pending.length) context origins pending)) := by
  have refined := location_refined frame request patternCode pending.length consistent
  simp only [ready, location, calling, initial, query] at refined
  cases handle : request.handle <;> simp only [handle, Effects.handleValue] at refined ⊢ <;>
    simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
      ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
      placed, initial, source, query, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, callable,
      StdLib.known, Eval.ioHead, callArguments, freshSlots, List.range_succ, Eval.argumentIsRaw,
      StdLib.rawArgument, ready, location, calling, handle, Effects.handleValue, refined]

def acceptedBindings (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat) : Equations :=
  (ready frame request patternCode kept).bindings ++ [(request.payload, .var frame.output)]

theorem answer_refined (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat)
    (consistent : ∃ environment, Solves environment frame.bindings) (fresh : FreshFor frame.output frame.bindings) :
    refine (ready frame request patternCode kept).bindings request.payload (.var frame.output) =
      some (acceptedBindings frame request patternCode kept) := by
  apply ClosedOnceQueryFrame.refine_fresh_closed
  · intro pair member
    rcases List.mem_append.mp member with old | added
    · exact fresh pair old
    · have same := List.mem_singleton.mp added
      subst pair
      simpa [LiteralQuerySource.handle_freeVars, encode, Mettapedia.Logic.LP.Term.freeVars] using
        (location_ne_output frame request patternCode kept).symm
  · exact ready_consistent frame request patternCode kept consistent
  · exact read_payload request

def answer (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat) (origins : List Nat) : CollectedAnswer :=
  ⟨request.payload, acceptedBindings frame request patternCode kept, origins ++ [0], []⟩

theorem answer_read (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat)
    (environment : Environment) (resolved : resolve (acceptedBindings frame request patternCode kept) = some environment) :
    read environment (.var frame.output) = request.payload := by
  have bound := resolve_sound resolved (request.payload, .var frame.output) (List.mem_append_right _ (by simp))
  rw [read_payload] at bound
  exact bound.symm

theorem ready_hit {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (request : Request) (patternCode : Atom)
    (consistent : ∃ environment, Solves environment frame.bindings) (fresh : FreshFor frame.output frame.bindings)
    (models : ∀ model, Solves model frame.bindings → read model patternCode = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) (present : request.pattern ∈ rows) :
    (ScopedQuerySource.machine .relational program).run 5
      (placed allocator world scope parents (ready frame request patternCode pending.length) context origins pending) =
      (if scope.caller.isNone then [answer frame request patternCode pending.length origins] else [],
        .exhausted (allocator, ⟨world, EagerDFS.Scope.record scope pending
          (answer frame request patternCode pending.length origins) :: parents⟩)) := by
  obtain ⟨environment, resolved⟩ := resolve_complete (ready_consistent frame request patternCode pending.length consistent)
  have refined := answer_refined frame request patternCode pending.length consistent fresh
  obtain ⟨afterEnvironment, afterResolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
  have actual := ScopedQuerySource.Guards.literal_first_prefix .relational program allocator world
    {scope with frontier := (ready frame request patternCode pending.length, context, origins) :: pending} parents
    (ready frame request patternCode pending.length) context origins [] pending frame.boundary
    (.var (location frame request patternCode pending.length)) patternCode (.var frame.output) request rows
    environment afterEnvironment (acceptedBindings frame request patternCode pending.length) rfl rfl rfl resolved
    (ready_location frame request patternCode pending.length environment resolved)
    (ready_pattern frame request patternCode pending.length models environment resolved) snapshot closed present refined afterResolved
  simpa [placed, ready, calling, initial, answer, EagerDFS.Scope.record,
    answer_read frame request patternCode pending.length afterEnvironment afterResolved] using actual

theorem ready_miss {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (request : Request) (patternCode : Atom)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (models : ∀ model, Solves model frame.bindings → read model patternCode = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) (absent : request.pattern ∉ rows) :
    (ScopedQuerySource.machine .relational program).step
      (placed allocator world scope parents (ready frame request patternCode pending.length) context origins pending) =
      some (.silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  obtain ⟨environment, resolved⟩ := resolve_complete (ready_consistent frame request patternCode pending.length consistent)
  exact ScopedQuerySource.Caller.literal_absence_step .relational program allocator world _ parents
    (ready frame request patternCode pending.length) context origins pending
    (.var (location frame request patternCode pending.length)) patternCode (.var frame.output)
    [.commit, .restoreCommit frame.boundary] environment request rows rfl rfl resolved
    (ready_location frame request patternCode pending.length environment resolved)
    (ready_pattern frame request patternCode pending.length models environment resolved) snapshot closed absent

/-- Start at the authored `once (match ...)`, not a pre-substituted query.
The actual principal solver supplies the closed pattern reading. Both branches
retain the reached caller, and a hit records its original prepared bindings. -/
theorem source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (request : Request) (patternCode : Atom)
    (principal : Environment) (resolved : resolve frame.bindings = some principal)
    (reading : read principal patternCode = request.pattern) (fresh : FreshFor frame.output frame.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    (ScopedQuerySource.machine .relational program).run (if present then 10 else 6)
      (placed allocator world scope parents (initial frame request patternCode) context origins pending) =
      (if present then (if scope.caller.isNone then [answer frame request patternCode pending.length origins] else []) else [],
        .exhausted (allocator, ⟨world,
          (if present then EagerDFS.Scope.record scope pending (answer frame request patternCode pending.length origins)
            else {scope with frontier := pending}) :: parents⟩)) := by
  have consistent : ∃ environment, Solves environment frame.bindings := ⟨principal, resolve_sound resolved⟩
  have models := principal_pattern_forces resolved patternCode request reading
  have entry := entry_prefix program allocator world scope parents frame context origins pending request patternCode consistent
  by_cases present : request.pattern ∈ rows
  · have hit := ready_hit program allocator world scope parents frame context origins pending request patternCode
      consistent fresh models rows snapshot closed present
    have combined := (ScopedQuerySource.machine .relational program).established_and_pending 5 5 _ _ [] entry
    rw [hit] at combined
    simpa [present] using combined
  · have missed := ready_miss program allocator world scope parents frame context origins pending request patternCode
      consistent models rows snapshot closed present
    have combined := (ScopedQuerySource.machine .relational program).established_and_pending 5 1 _ _ [] entry
    rw [Machine.run_succ_silent _ missed] at combined
    simpa [present, Machine.run] using combined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSource
