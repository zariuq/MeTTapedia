import Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiteralQuerySource
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# First-witness queries in retained source frames

The result name and reached equations come from the caller, not a fixed
root invocation. A fresh result extends any satisfiable inherited equations.
The source name allocator supplies the separate location slot. Older scopes,
answer occurrences and alternatives are retained by the existing scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request query expression read_pattern read_payload read_handle)

def FreshFor (name : String) (bindings : Equations) : Prop :=
  ∀ pair ∈ bindings, name ∉ (encode pair.1).freeVars ∧ name ∉ (encode pair.2).freeVars

instance (name : String) (bindings : Equations) : Decidable (FreshFor name bindings) := by
  unfold FreshFor
  infer_instance

theorem read_update (environment : Environment) (name : String) (value atom : Atom)
    (fresh : name ∉ (encode atom).freeVars) :
    EagerDFS.Destination.read (Function.update environment name (encode value)) atom =
      EagerDFS.Destination.read environment atom := by
  unfold EagerDFS.Destination.read
  congr 1
  apply Mettapedia.Logic.LP.Subst.applyTerm_congr
  intro other member
  have apart : other ≠ name := by
    intro equal
    exact fresh (equal ▸ member)
  exact Function.update_of_ne apart (encode value) environment

theorem solves_update (environment : Environment) (bindings : Equations) (name : String)
    (value : Atom) (fresh : FreshFor name bindings) (solved : Solves environment bindings) :
    Solves (Function.update environment name (encode value)) bindings := by
  intro pair member
  rw [read_update environment name value pair.1 (fresh pair member).1,
    read_update environment name value pair.2 (fresh pair member).2]
  exact solved pair member

/-- The new equation is solved by extending an old model at an unused name. -/
theorem refine_fresh_closed (bindings : Equations) (name : String) (value : Atom)
    (fresh : FreshFor name bindings) (consistent : ∃ environment, Solves environment bindings)
    (closed : ∀ environment, EagerDFS.Destination.read environment value = value) :
    refine bindings value (.var name) = some (bindings ++ [(value, .var name)]) := by
  obtain ⟨environment, solved⟩ := consistent
  apply (refine_iff _ _ _ _).mpr
  refine ⟨rfl, Function.update environment name (encode value),
    solves_update environment bindings name value fresh solved, ?_⟩
  calc
    EagerDFS.Destination.read (Function.update environment name (encode value)) value = value := closed _
    _ = EagerDFS.Destination.read (Function.update environment name (encode value)) (.var name) := by
      simp only [EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.applyTerm]
      exact (congrArg decode (Function.update_self name (encode value) environment)).trans (decode_encode value) |>.symm

theorem refined_consistent (bindings : Equations) (value destination : Atom)
    (accepted : refine bindings value destination = some (bindings ++ [(value, destination)])) :
    ∃ environment, Solves environment (bindings ++ [(value, destination)]) := by
  obtain ⟨_, environment, solved, result⟩ := (refine_iff _ _ _ _).mp accepted
  exact ⟨environment, (solves_append_equation _ _ _ _).mpr ⟨solved, result⟩⟩

theorem fold_support_iff (atoms : List Atom) (initial : Finset String) (name : String) :
    name ∈ atoms.foldl (fun names atom => names ∪ (encode atom).freeVars) initial ↔
      name ∈ initial ∨ ∃ atom ∈ atoms, name ∈ (encode atom).freeVars := by
  induction atoms generalizing initial with
  | nil => simp
  | cons atom rest ih =>
      simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
      aesop

theorem binding_names_in_support (control : Control) (pair : Atom × Atom)
    (member : pair ∈ control.bindings) :
    (encode pair.1).freeVars ∪ (encode pair.2).freeVars ⊆ control.support := by
  intro name occurs
  apply Finset.mem_union_right
  apply (fold_support_iff _ _ name).mpr
  right
  rcases Finset.mem_union.mp occurs with left | right
  · exact ⟨pair.1, List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨pair, member, by simp⟩)), left⟩
  · exact ⟨pair.2, List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨pair, member, by simp⟩)), right⟩

/-- Retaining equations and pending goals retains their source-name support. -/
theorem support_mono (before after : Control)
    (destination : before.destination = after.destination)
    (reserved : before.reserved ⊆ after.reserved)
    (bindings : before.bindings ⊆ after.bindings)
    (goals : before.goals ⊆ after.goals) : before.support ⊆ after.support := by
  intro name member
  rcases Finset.mem_union.mp member with kept | used
  · exact Finset.mem_union_left _ (reserved kept)
  · apply Finset.mem_union_right
    obtain ⟨atom, present, occurs⟩ := (fold_support_iff _ _ name).mp used |>.resolve_left (by simp)
    apply (fold_support_iff _ _ name).mpr
    refine Or.inr ⟨atom, ?_, occurs⟩
    rcases List.mem_cons.mp present with output | later
    · exact List.mem_cons.mpr (Or.inl (output.trans destination))
    · apply List.mem_cons_of_mem
      rcases List.mem_append.mp later with binding | goal
      · obtain ⟨pair, present, field⟩ := List.mem_flatMap.mp binding
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨pair, bindings present, field⟩)
      · obtain ⟨entry, present, field⟩ := List.mem_flatMap.mp goal
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry, goals present, field⟩)

theorem fresh_for_bindings (control : Control) (name : String) (fresh : name ∉ control.support) :
    FreshFor name control.bindings := by
  intro pair member
  exact ⟨fun occurs => fresh (binding_names_in_support control pair member
    (Finset.mem_union_left _ occurs)), fun occurs => fresh
    (binding_names_in_support control pair member (Finset.mem_union_right _ occurs))⟩

/-- Solving the reached equations leaves an unused result slot unbound. -/
theorem fresh_read (bindings : Equations) (name : String) (environment : Environment)
    (fresh : FreshFor name bindings) (resolved : resolve bindings = some environment) :
    EagerDFS.Destination.read environment (.var name) = .var name := by
  have relevant := Mettapedia.Logic.LP.unifyTotal_relevantIdempotent (equations bindings) environment resolved
  have outside : name ∉ Mettapedia.Logic.LP.eqVars (equations bindings) := by
    intro occurs
    obtain ⟨pair, member, used⟩ := (Mettapedia.Logic.LP.mem_eqVars (equations := equations bindings)).mp occurs
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact used.elim (fresh original present).1 (fresh original present).2
  have fixed := relevant.fixes name outside
  simpa only [EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.applyTerm, decode] using
    congrArg decode fixed

structure Frame where
  bindings : Equations
  output : String
  reserved : Finset String := ∅
  boundary : Nat := 0

def initial (frame : Frame) (request : Request) : Control :=
  {bindings := frame.bindings, destination := .var frame.output, reserved := frame.reserved,
   cutBoundary := frame.boundary, goals := [.evaluate (expression request) (.var frame.output)]}

def calling (frame : Frame) (request : Request) (kept : Nat) : Control :=
  { (initial frame request) with
    cutBoundary := kept
    goals := [.evaluate (query request) (.var frame.output), .commit, .restoreCommit frame.boundary] }

def location (frame : Frame) (request : Request) (kept : Nat) : String :=
  freshName (calling frame request kept) 0

def ready (frame : Frame) (request : Request) (kept : Nat) : Control :=
  { (calling frame request kept) with
   bindings := frame.bindings ++ [(Effects.handleValue request.handle, .var (location frame request kept))],
   goals := [.invoke "match" [.var (location frame request kept), request.pattern,
     request.payload] (.var frame.output), .commit, .restoreCommit frame.boundary]}

theorem location_fresh (frame : Frame) (request : Request) (kept : Nat) :
    FreshFor (location frame request kept) frame.bindings :=
  fresh_for_bindings (calling frame request kept) _ (freshName_not_mem _ _)

theorem location_ne_output (frame : Frame) (request : Request) (kept : Nat) :
    location frame request kept ≠ frame.output := by
  intro equal
  have fresh := freshName_not_mem (calling frame request kept) 0
  apply fresh
  change location frame request kept ∈ _
  rw [equal]
  apply Finset.mem_union_right
  apply (fold_support_iff _ _ _).mpr
  exact Or.inr ⟨.var frame.output, by simp [calling, initial], by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

theorem location_refined (frame : Frame) (request : Request) (kept : Nat)
    (consistent : ∃ environment, Solves environment frame.bindings) :
    refine frame.bindings (Effects.handleValue request.handle) (.var (location frame request kept)) =
      some (ready frame request kept).bindings :=
  refine_fresh_closed _ _ _ (location_fresh frame request kept) consistent (read_handle request.handle)

theorem ready_consistent (frame : Frame) (request : Request) (kept : Nat)
    (consistent : ∃ environment, Solves environment frame.bindings) :
    ∃ environment, Solves environment (ready frame request kept).bindings :=
  refined_consistent _ _ _ (location_refined frame request kept consistent)

theorem output_fresh_ready (frame : Frame) (request : Request) (kept : Nat)
    (fresh : FreshFor frame.output frame.bindings) :
    FreshFor frame.output (ready frame request kept).bindings := by
  intro pair member
  rcases List.mem_append.mp member with old | added
  · exact fresh pair old
  · have equal := List.mem_singleton.mp added
    subst pair
    simpa [LiteralQuerySource.handle_freeVars, encode, Mettapedia.Logic.LP.Term.freeVars] using
      (location_ne_output frame request kept).symm

def acceptedBindings (frame : Frame) (request : Request) (kept : Nat) : Equations :=
  (ready frame request kept).bindings ++ [(request.payload, .var frame.output)]

theorem answer_refined (frame : Frame) (request : Request) (kept : Nat)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (fresh : FreshFor frame.output frame.bindings) :
    refine (ready frame request kept).bindings (request.payload) (.var frame.output) =
      some (acceptedBindings frame request kept) :=
  refine_fresh_closed _ _ _ (output_fresh_ready frame request kept fresh)
    (ready_consistent frame request kept consistent) (read_payload request)

theorem ready_operands (frame : Frame) (request : Request) (kept : Nat)
    (environment : Environment) (resolved : resolve (ready frame request kept).bindings = some environment) :
    [.var (location frame request kept), request.pattern, request.payload].map
      (EagerDFS.Destination.read environment) = [Effects.handleValue request.handle, request.pattern, request.payload] := by
  have bound := resolve_sound resolved (Effects.handleValue request.handle, .var (location frame request kept))
    (List.mem_append_right _ (by simp))
  simp only [List.map_cons, List.map_nil, read_pattern, read_payload]
  rw [← bound, (read_handle request.handle)]

theorem answer_read (frame : Frame) (request : Request) (kept : Nat)
    (environment : Environment)
    (resolved : resolve (acceptedBindings frame request kept) = some environment) :
    EagerDFS.Destination.read environment (.var frame.output) = request.payload := by
  have bound := resolve_sound resolved (request.payload, .var frame.output)
    (List.mem_append_right _ (by simp))
  rw [← bound, read_payload]

def placed {Context : Type} (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) : ScopedCursor Context :=
  (allocator, ⟨world, {scope with frontier := (control, context, origins) :: pending} :: parents⟩)

set_option maxHeartbeats 1000000 in
theorem entry_to_invocation {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 5
      (placed allocator world scope parents (initial frame request) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (ready frame request pending.length) context origins pending)) := by
  have refined := location_refined frame request pending.length consistent
  simp only [ready, location, calling, initial, query] at refined
  cases handle : request.handle <;> simp only [handle, Effects.handleValue] at refined ⊢ <;>
    simp [Machine.run, EagerDFSStreaming.machine, placed, initial, expression, query,
    scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine, prepare, replace,
    installChild, retainChild, callable, StdLib.known, Eval.ioHead,
    callArguments, freshSlots, List.range_succ, Eval.argumentIsRaw, StdLib.rawArgument,
    ready, location, calling, handle, Effects.handleValue, refined]

def answer (frame : Frame) (request : Request) (kept : Nat)
    (origins : List Nat) : CollectedAnswer :=
  ⟨request.payload, acceptedBindings frame request kept, origins ++ [0], []⟩

theorem ready_hit {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (fresh : FreshFor frame.output frame.bindings) (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (present : request.pattern ∈ rows) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 5
      (placed allocator world scope parents (ready frame request pending.length) context origins pending) =
      (if scope.caller.isNone then [answer frame request pending.length origins] else [],
       .exhausted (allocator, ⟨world, EagerDFS.Scope.record scope pending
         (answer frame request pending.length origins) :: parents⟩)) := by
  obtain ⟨environment, resolved⟩ := resolve_complete (ready_consistent frame request pending.length consistent)
  have refined := answer_refined frame request pending.length consistent fresh
  obtain ⟨afterEnvironment, afterResolved⟩ := resolve_complete (refined_consistent _ _ _ refined)
  cases found : FirstQueryCursor.reference [] (request.pattern) (0, rows) with
  | none => exact False.elim (((LiteralQuerySource.reference_absent request rows).mp found) present)
  | some entry =>
      have searched : (FirstQueryCursor.machine [] (request.pattern)).run (rows.length + 1)
          (0, rows) = ([], .finished (some entry)) := by
        rw [FirstQueryCursor.complete, found]
      let readyScope : CollectionScope Context := {scope with frontier :=
        (ready frame request pending.length, context, origins) :: pending}
      have actual := ConstantQuerySource.first_query_prefix .relational program allocator world readyScope parents
        (ready frame request pending.length) context origins [] pending frame.boundary
        [.var (location frame request pending.length), request.pattern, request.payload]
        (.var frame.output) request.pattern request.payload request.scalar request.handle rows (rows.length + 1)
        entry environment afterEnvironment (acceptedBindings frame request pending.length)
        rfl rfl rfl resolved (ready_operands frame request pending.length environment resolved)
        snapshot searched refined afterResolved
      simpa [placed, readyScope, ready, calling, initial, answer, EagerDFS.Scope.record,
        answer_read frame request pending.length afterEnvironment afterResolved] using actual

theorem ready_miss {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows) (absent : request.pattern ∉ rows) :
    scopeStep .relational program
      (placed allocator world scope parents (ready frame request pending.length) context origins pending) =
      .silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩) := by
  obtain ⟨environment, resolved⟩ := resolve_complete (ready_consistent frame request pending.length consistent)
  have searched : (FirstQueryCursor.machine [] (request.pattern)).run (rows.length + 1)
      (0, rows) = ([], .finished none) := by
    rw [FirstQueryCursor.complete, (LiteralQuerySource.reference_absent request rows).mpr absent]
  let readyScope : CollectionScope Context := {scope with frontier :=
    (ready frame request pending.length, context, origins) :: pending}
  have actual := ConstantQuerySource.empty_query_keeps_outer_work .relational program allocator world readyScope parents
    (ready frame request pending.length) context origins pending
    [.var (location frame request pending.length), request.pattern, request.payload]
    (.var frame.output) request.pattern request.payload [.commit, .restoreCommit frame.boundary]
    request.handle rows (rows.length + 1) environment rfl rfl resolved
    (ready_operands frame request pending.length environment resolved) snapshot searched
  simpa [placed, readyScope] using actual

theorem source_hit_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (fresh : FreshFor frame.output frame.bindings) (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (present : request.pattern ∈ rows) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 10
      (placed allocator world scope parents (initial frame request) context origins pending) =
      (if scope.caller.isNone then [answer frame request pending.length origins] else [],
       .exhausted (allocator, ⟨world, EagerDFS.Scope.record scope pending
         (answer frame request pending.length origins) :: parents⟩)) := by
  have composed := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).established_and_pending
    5 5 _ _ [] (entry_to_invocation program allocator world scope parents frame context origins pending
      request consistent)
  simpa [ready_hit program allocator world scope parents frame context origins pending request
    consistent fresh rows snapshot present] using composed

theorem source_miss_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows) (absent : request.pattern ∉ rows) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 6
      (placed allocator world scope parents (initial frame request) context origins pending) =
      ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  have step : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step
      (placed allocator world scope parents (ready frame request pending.length) context origins pending) =
      some (.silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
    rw [EagerDFSStreaming.Scoped.step_scope, ready_miss program allocator world scope parents frame context origins pending
      request consistent rows snapshot absent]
  have composed := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).established_and_pending
    5 1 _ _ [] (entry_to_invocation program allocator world scope parents frame context origins pending
      request consistent)
  simpa [Machine.run, step] using composed

/-- A missing selected space preserves the source fault boundary and the
entire reached cursor. It is not a completed empty query. -/
theorem ready_missing {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (missing : world.state.read request.handle = none) :
    scopeStep .relational program
      (placed allocator world scope parents (ready frame request pending.length) context origins pending) =
      .call (.fault .invalidSpace)
        (placed allocator world scope parents (ready frame request pending.length) context origins pending) := by
  obtain ⟨environment, resolved⟩ := resolve_complete (ready_consistent frame request pending.length consistent)
  let readyScope : CollectionScope Context := {scope with frontier :=
    (ready frame request pending.length, context, origins) :: pending}
  have applied : StdLib.apply world.state "match"
      ([.var (location frame request pending.length), request.pattern, request.payload].map
        (EagerDFS.Destination.read environment)) = .error .invalidSpace := by
    rw [ready_operands frame request pending.length environment resolved]
    change (match Effects.readHandle (Effects.handleValue request.handle) >>= world.state.read with
      | some rows => Except.ok (world.state, SpaceSemantics.query rows request.pattern (request.payload))
      | none => Except.error Effects.Fault.invalidSpace) = _
    simp [missing]
  exact scope_primitive_fault .relational program allocator world readyScope parents
    (ready frame request pending.length) context origins pending "match"
    [.var (location frame request pending.length), request.pattern, request.payload]
    (.var frame.output) [.commit, .restoreCommit frame.boundary] environment .invalidSpace
    rfl rfl resolved (by decide) applied

theorem source_missing_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (frame : Frame) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (request : Request)
    (consistent : ∃ environment, Solves environment frame.bindings)
    (missing : world.state.read request.handle = none) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 6
      (placed allocator world scope parents (initial frame request) context origins pending) =
      ([], .suspended (.fault .invalidSpace)
        (placed allocator world scope parents (ready frame request pending.length) context origins pending)) := by
  have step : (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).step
      (placed allocator world scope parents (ready frame request pending.length) context origins pending) =
      some (.call (.fault .invalidSpace)
        (placed allocator world scope parents (ready frame request pending.length) context origins pending)) := by
    rw [EagerDFSStreaming.Scoped.step_scope, ready_missing program allocator world scope parents frame context origins pending
      request consistent missing]
  have composed := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).established_and_pending
    5 1 _ _ [] (entry_to_invocation program allocator world scope parents frame context origins pending request consistent)
  simpa [Machine.run, step] using composed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryFrame
