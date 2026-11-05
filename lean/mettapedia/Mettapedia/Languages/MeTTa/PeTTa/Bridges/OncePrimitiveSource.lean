import Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming

/-!
# A primitive first answer reaches the actual scoped once boundary

The source primitive supplies its ordered occurrences, the first is refined
against the actual destination, and the maintained commit operation removes
only alternatives inside the saved floor. Shared effects already performed
by the primitive remain. No completion hypothesis concerns discarded sibling
branches or older caller work.

The five inspections below begin at the prepared invocation, not at source
text entry. Primitive computation, operand preparation, row traversal and
native execution have separate cost accounts. This is a scoped source law,
not an equivalence between the eager and destination profiles.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.OncePrimitiveSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination

def laterWork {Context : Type} (control : Control) (context : Context) (origins : List Nat)
    (destination : Atom) (older : List Goal) (values : List Atom) : List (CollectionWork Context) :=
  (values.zipIdx 1).map fun (value, index) =>
    ({control with goals := .equate value destination :: older}, context, origins ++ [index])

theorem primitive_cons {Context : Type} (control : Control) (context : Context) (origins : List Nat)
    (destination : Atom) (older : List Goal) (value : Atom) (values : List Atom) :
    primitiveWork control context origins destination older (value :: values) =
      ({control with goals := .equate value destination :: older}, context, origins ++ [0]) ::
        laterWork control context origins destination older values := by
  simp [primitiveWork, laterWork, List.zipIdx_cons]

theorem first_answer_prefix {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (inside kept : List (CollectionWork Context)) (previousBoundary : Nat)
    (head : String) (arguments : List Atom) (destination value : Atom) (values : List Atom)
    (environment afterEnvironment : Environment) (bindings : Equations) (state : Effects.State)
    (frontier : scope.frontier = (control, context, origins) :: inside ++ kept)
    (atCall : control.goals = [.invoke head arguments destination, .commit, .restoreCommit previousBoundary])
    (boundary : control.cutBoundary = kept.length)
    (resolved : resolve control.bindings = some environment)
    (known : StdLib.known head = true) (ordinary : head ≠ "parse")
    (applied : StdLib.apply world.state head (arguments.map (read environment)) = .ok (state, value :: values))
    (refined : refine control.bindings value destination = some bindings)
    (afterResolved : resolve bindings = some afterEnvironment) :
    let answer : CollectedAnswer := ⟨read afterEnvironment control.destination, bindings, origins ++ [0], []⟩
    let after : ScopedCursor Context :=
      (allocator, ⟨{world with state}, EagerDFS.Scope.record scope kept answer :: parents⟩)
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run 5
      (allocator, ⟨world, scope :: parents⟩) =
      (if scope.caller.isNone then [answer] else [], .exhausted after) := by
  let older : List Goal := [.commit, .restoreCommit previousBoundary]
  let firstControl : Control := {control with goals := .equate value destination :: older}
  let accepted : Control := {control with bindings, goals := older}
  let younger := laterWork control context origins destination older values ++ inside
  let scope₁ : CollectionScope Context :=
    {scope with frontier := (firstControl, context, origins ++ [0]) :: younger ++ kept}
  let scope₂ : CollectionScope Context :=
    {scope with frontier := (accepted, context, origins ++ [0]) :: younger ++ kept}
  have invoked := scope_primitive_success policy program allocator world scope parents control context origins
    (inside ++ kept) head arguments destination older environment state (value :: values)
    frontier atCall resolved known ordinary applied
  have invocation : scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨{world with state}, scope₁ :: parents⟩) := by
    simpa [primitive_cons, scope₁, firstControl, younger, List.append_assoc] using invoked
  have refinement : scopeStep policy program (allocator, ⟨{world with state}, scope₁ :: parents⟩) =
      .silent (allocator, ⟨{world with state}, scope₂ :: parents⟩) := by
    simp [scopeStep, scope₁, scope₂, firstControl, accepted, older, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, refined, installChild, retainChild]
  have committed := EagerDFSStreaming.Scoped.commit_first_answer policy program allocator
    {world with state} scope₂ parents accepted context (origins ++ [0]) younger kept previousBoundary
    afterEnvironment rfl rfl boundary afterResolved
  have firstStep : (EagerDFSStreaming.machine program (.scopedDestination Context policy)).step
      (allocator, ⟨world, scope :: parents⟩) = some (.silent (allocator, ⟨{world with state}, scope₁ :: parents⟩)) := by
    rw [EagerDFSStreaming.Scoped.step_scope, invocation]
  have secondStep : (EagerDFSStreaming.machine program (.scopedDestination Context policy)).step
      (allocator, ⟨{world with state}, scope₁ :: parents⟩) =
      some (.silent (allocator, ⟨{world with state}, scope₂ :: parents⟩)) := by
    rw [EagerDFSStreaming.Scoped.step_scope, refinement]
  rw [(EagerDFSStreaming.machine program (.scopedDestination Context policy)).run_succ_silent firstStep,
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run_succ_silent secondStep]
  simpa [scope₂, accepted, EagerDFS.Scope.record] using committed

/-- No answers removes the current primitive branch, not the caller's older
alternatives and not the reached world. This is not whole-scope exhaustion. -/
theorem empty_primitive_keeps_outer_work {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) (state : Effects.State)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (known : StdLib.known head = true) (ordinary : head ≠ "parse")
    (applied : StdLib.apply world.state head (arguments.map (read environment)) = .ok (state, [])) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨{world with state}, {scope with frontier := pending} :: parents⟩) := by
  simpa [primitiveWork] using scope_primitive_success policy program allocator world scope parents control context
    origins pending head arguments destination older environment state [] frontier atCall resolved known ordinary applied

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.OncePrimitiveSource
