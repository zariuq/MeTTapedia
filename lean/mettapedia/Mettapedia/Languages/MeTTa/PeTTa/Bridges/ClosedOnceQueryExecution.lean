import Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQuerySource

/-!
# Closed tagged queries from actual once syntax

This family starts at the scoped source evaluator's evaluation goal, not a
prepared primitive invocation. Its pattern is a closed formula/state pair.
The shared world and identity allocator are explicit parameters. Native
open-fact admission and the full temporal-logic driver remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination

variable (program : SpaceSemantics.Program)
def pattern (relation : String) (formula node : Int) : Atom :=
  .expression [.symbol relation, .grounded (.int formula), .grounded (.int node)]
def query (relation : String) (formula node : Int) : Atom :=
  .expression [.symbol "match", .symbol "&self", pattern relation formula node, Effects.boolean true]
def expression (relation : String) (formula node : Int) : Atom := .expression [.symbol "once", query relation formula node]

def initialControl (relation : String) (formula node : Int) : Control :=
  {bindings := [], goals := [.evaluate (expression relation formula node) (.var "answer")], destination := .var "answer"}

def root (allocator : Allocator) (world : World) (control : Control) : ScopedCursor Unit :=
  (allocator, ⟨world, [{frontier := [(control, (), [])]}]⟩)

def callControl (relation : String) (formula node : Int) : Control :=
  {bindings := [], goals := [.evaluate (query relation formula node) (.var "answer"), .commit, .restoreCommit 0],
    destination := .var "answer"}

def locationName (relation : String) (formula node : Int) : String := freshName (callControl relation formula node) 0

def readyControl (relation : String) (formula node : Int) : Control :=
  {bindings := [(.symbol "&self", .var (locationName relation formula node))],
   goals := [.invoke "match" [.var (locationName relation formula node), pattern relation formula node, Effects.boolean true] (.var "answer"),
     .commit, .restoreCommit 0], destination := .var "answer"}

theorem refine_location (name : String) : refine [] (.symbol "&self") (.var name) =
    some [(.symbol "&self", .var name)] := by
  apply (refine_iff _ _ _ _).mpr
  refine ⟨rfl, (fun _ => encode (.symbol "&self")), ?_, ?_⟩
  · intro pair member
    cases member
  · simp [EagerDFS.Destination.read, encode, Mettapedia.Logic.LP.Subst.applyTerm]

set_option maxHeartbeats 1000000 in
theorem entry_to_invocation (allocator : Allocator) (world : World) (relation : String) (formula node : Int) :
    (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run 5
      (root allocator world (initialControl relation formula node)) =
      ([], .exhausted (root allocator world (readyControl relation formula node))) := by
  simp [Machine.run, EagerDFSStreaming.machine, root, initialControl, expression, query,
    scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine, prepare, replace,
    installChild, retainChild, callable, StdLib.known, Eval.ioHead,
    callArguments, freshSlots, List.range_succ, Eval.argumentIsRaw, StdLib.rawArgument,
    readyControl, locationName, callControl, refine_location]

theorem location_fresh (relation : String) (formula node : Int) : locationName relation formula node ≠ "answer" := by
  have fresh := freshName_not_mem (callControl relation formula node) 0
  intro same
  apply fresh
  rw [← locationName, same]
  simp [Control.support, callControl, Goal.atoms, encode, pattern, query,
    Mettapedia.Logic.LP.Term.freeVars]

theorem read_pattern (environment : Environment) (relation : String) (formula node : Int) :
    EagerDFS.Destination.read environment (pattern relation formula node) = pattern relation formula node := by
  simp [EagerDFS.Destination.read, pattern, encode, decode,
    List.ofFn_succ]

theorem read_true (environment : Environment) :
    EagerDFS.Destination.read environment (Effects.boolean true) = Effects.boolean true := by
  simp [EagerDFS.Destination.read, Effects.boolean, encode, decode]

theorem read_location (environment : Environment) :
    EagerDFS.Destination.read environment (.symbol "&self") = .symbol "&self" := by
  simp [EagerDFS.Destination.read, encode, decode]

def acceptedBindings (relation : String) (formula node : Int) : Equations :=
  (readyControl relation formula node).bindings ++ [(Effects.boolean true, .var "answer")]

def satisfying : Environment := fun name =>
  if name = "answer" then encode (Effects.boolean true) else encode (.symbol "&self")

theorem ready_model (relation : String) (formula node : Int) : Solves satisfying (readyControl relation formula node).bindings := by
  intro pair member
  have same : pair = (.symbol "&self", .var (locationName relation formula node)) := by simpa [readyControl] using member
  subst pair
  simp [EagerDFS.Destination.read, encode, satisfying, location_fresh]

theorem accepted_model (relation : String) (formula node : Int) : Solves satisfying (acceptedBindings relation formula node) := by
  intro pair member
  rcases List.mem_append.mp member with old | added
  · exact ready_model relation formula node pair old
  · have same : pair = (Effects.boolean true, .var "answer") := List.mem_singleton.mp added
    subst pair
    simp [EagerDFS.Destination.read, encode, satisfying, Effects.boolean]

theorem accepted_refine (relation : String) (formula node : Int) :
    refine (readyControl relation formula node).bindings (Effects.boolean true) (.var "answer") =
      some (acceptedBindings relation formula node) := by
  apply (refine_iff _ _ _ _).mpr
  refine ⟨rfl, satisfying, ready_model relation formula node, ?_⟩
  exact accepted_model relation formula node (Effects.boolean true, .var "answer") (by simp [acceptedBindings])

theorem ready_resolves (relation : String) (formula node : Int) :
    ∃ environment, resolve (readyControl relation formula node).bindings = some environment :=
  resolve_complete ⟨satisfying, ready_model relation formula node⟩

theorem accepted_resolves (relation : String) (formula node : Int) :
    ∃ environment, resolve (acceptedBindings relation formula node) = some environment :=
  resolve_complete ⟨satisfying, accepted_model relation formula node⟩

theorem ready_operands (relation : String) (formula node : Int) (environment : Environment)
    (resolved : resolve (readyControl relation formula node).bindings = some environment) :
    [.var (locationName relation formula node), pattern relation formula node, Effects.boolean true].map
      (EagerDFS.Destination.read environment) = [.symbol "&self", pattern relation formula node, Effects.boolean true] := by
  have bound := resolve_sound resolved (.symbol "&self", .var (locationName relation formula node)) (by simp [readyControl])
  simp only [List.map_cons, List.map_nil, read_pattern, read_true]
  rw [← bound, read_location]

theorem accepted_output (relation : String) (formula node : Int) (environment : Environment)
    (resolved : resolve (acceptedBindings relation formula node) = some environment) :
    EagerDFS.Destination.read environment (.var "answer") = Effects.boolean true := by
  have bound := resolve_sound resolved (Effects.boolean true, .var "answer") (by simp [acceptedBindings])
  rw [← bound, read_true]

theorem pattern_literal (relation : String) (formula node : Int) (ordinary : relation ≠ "cons") : SpaceSemantics.Literal (pattern relation formula node) := by
  apply SpaceSemantics.Literal.constructor relation _ ordinary
  intro atom member
  rcases List.mem_cons.mp member with same | member
  · subst atom
    exact .grounded _
  · have same := List.mem_singleton.mp member
    subst atom
    exact .grounded _

theorem reference_absent (relation : String) (formula node : Int) (rows : List Atom) (ordinary : relation ≠ "cons") :
    FirstQueryCursor.reference [] (pattern relation formula node) (0, rows) = none ↔ pattern relation formula node ∉ rows := by
  rw [FirstQueryCursor.absent_iff]
  simp [SpaceSemantics.matchValue_literal (pattern_literal relation formula node ordinary)]
  constructor
  · intro absent member
    exact absent _ member rfl
  · intro absent row member same
    exact absent (same.symm ▸ member)

def answer (relation : String) (formula node : Int) : CollectedAnswer :=
  ⟨Effects.boolean true, acceptedBindings relation formula node, [0], []⟩

def completedState (allocator : Allocator) (world : World) (relation : String) (formula node : Int) (present : Bool) : ScopedCursor Unit :=
  (allocator, ⟨world, [{frontier := [], collected := if present then [answer relation formula node] else []}]⟩)

theorem completed_step (allocator : Allocator) (world : World) (relation : String) (formula node : Int) (present : Bool) :
    scopeStep .relational program (completedState allocator world relation formula node present) =
      .finish (completedState allocator world relation formula node present) := rfl

theorem completed_run (allocator : Allocator) (world : World) (relation : String) (formula node : Int) (present : Bool) (fuel : Nat) :
    (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run (fuel + 1)
      (completedState allocator world relation formula node present) =
      ([], .finished (completedState allocator world relation formula node present)) := by
  simp [Machine.run, EagerDFSStreaming.machine, completed_step]

theorem ready_hit (allocator : Allocator) (world : World) (relation : String) (formula node : Int)
    (ordinary : relation ≠ "cons") (present : pattern relation formula node ∈ world.state.core) :
    (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run 5
      (root allocator world (readyControl relation formula node)) =
      ([answer relation formula node], .exhausted (completedState allocator world relation formula node true)) := by
  obtain ⟨environment, resolved⟩ := ready_resolves relation formula node
  obtain ⟨afterEnvironment, afterResolved⟩ := accepted_resolves relation formula node
  cases found : FirstQueryCursor.reference [] (pattern relation formula node) (0, world.state.core) with
  | none => exact False.elim (((reference_absent relation formula node world.state.core ordinary).mp found) present)
  | some entry =>
      have searched : (FirstQueryCursor.machine [] (pattern relation formula node)).run (world.state.core.length + 1)
          (0, world.state.core) = ([], .finished (some entry)) := by
        rw [FirstQueryCursor.complete, found]
      let scope : CollectionScope Unit := {frontier := [(readyControl relation formula node, (), [])]}
      have actual := OnceQuerySource.first_query_prefix .relational program allocator world scope []
        (readyControl relation formula node) () [] [] [] 0
        [.var (locationName relation formula node), pattern relation formula node, Effects.boolean true]
        (.var "answer") (pattern relation formula node) .self world.state.core (world.state.core.length + 1)
        entry environment afterEnvironment (acceptedBindings relation formula node) rfl rfl rfl resolved
        (ready_operands relation formula node environment resolved) rfl searched (accepted_refine relation formula node) afterResolved
      simpa [scope, root, readyControl, completedState, answer, EagerDFS.Scope.record,
        accepted_output relation formula node afterEnvironment afterResolved] using actual

theorem ready_miss_step (allocator : Allocator) (world : World) (relation : String) (formula node : Int)
    (ordinary : relation ≠ "cons") (absent : pattern relation formula node ∉ world.state.core) :
    scopeStep .relational program (root allocator world (readyControl relation formula node)) =
      .silent (completedState allocator world relation formula node false) := by
  obtain ⟨environment, resolved⟩ := ready_resolves relation formula node
  have searched : (FirstQueryCursor.machine [] (pattern relation formula node)).run (world.state.core.length + 1)
      (0, world.state.core) = ([], .finished none) := by
    rw [FirstQueryCursor.complete, (reference_absent relation formula node world.state.core ordinary).mpr absent]
  let scope : CollectionScope Unit := {frontier := [(readyControl relation formula node, (), [])]}
  have actual := OnceQuerySource.empty_query_keeps_outer_work .relational program allocator world scope []
    (readyControl relation formula node) () [] []
    [.var (locationName relation formula node), pattern relation formula node, Effects.boolean true]
    (.var "answer") (pattern relation formula node) [.commit, .restoreCommit 0] .self world.state.core
    (world.state.core.length + 1) environment rfl rfl resolved
    (ready_operands relation formula node environment resolved) rfl searched
  simpa [scope, root, completedState] using actual

theorem ready_finishes (allocator : Allocator) (world : World) (relation : String) (formula node : Int)
    (ordinary : relation ≠ "cons") :
    (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run 6
      (root allocator world (readyControl relation formula node)) =
      (if pattern relation formula node ∈ world.state.core then [answer relation formula node] else [],
       .finished (completedState allocator world relation formula node (decide (pattern relation formula node ∈ world.state.core)))) := by
  by_cases present : pattern relation formula node ∈ world.state.core
  · have resumed := (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).established_and_pending
      5 1 (root allocator world (readyControl relation formula node)) (completedState allocator world relation formula node true)
      [answer relation formula node] (ready_hit program allocator world relation formula node ordinary present)
    simpa [completed_run program allocator world relation formula node true 0, present] using resumed
  · have step : (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).step
        (root allocator world (readyControl relation formula node)) =
        some (.silent (completedState allocator world relation formula node false)) := by
      rw [EagerDFSStreaming.Scoped.step_scope, ready_miss_step program allocator world relation formula node ordinary present]
    rw [(EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run_succ_silent step]
    simpa [present] using completed_run program allocator world relation formula node false 4

/-- The complete source expression terminates for every finite source row
list. Its result is a single true answer or no answer, and the reached world
and allocator are preserved exactly. The bound is on source control steps. -/
theorem source_finishes (allocator : Allocator) (world : World) (relation : String) (formula node : Int)
    (ordinary : relation ≠ "cons") :
    (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run 11
      (root allocator world (initialControl relation formula node)) =
      (if pattern relation formula node ∈ world.state.core then [answer relation formula node] else [],
       .finished (completedState allocator world relation formula node (decide (pattern relation formula node ∈ world.state.core)))) := by
  have resumed := (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).established_and_pending
    5 6 (root allocator world (initialControl relation formula node)) (root allocator world (readyControl relation formula node)) []
    (entry_to_invocation program allocator world relation formula node)
  simpa [ready_finishes program allocator world relation formula node ordinary] using resumed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryExecution
