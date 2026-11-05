import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ConstantQuerySource

/-!
# First-query evidence at the scoped source invocation

The query template is the literal Boolean true, so it has no body effects or
additional search. A cursor hit supplies the first primitive answer; a cursor
miss supplies an empty primitive result only after complete traversal.
The existing scoped evaluator retains the caller floor and reached world.

This uses the scoped primitive profile. General body-evaluating match,
open-fact runtime conformance and source operand preparation are not inferred
from this boundary theorem. Row-probe costs and its five control inspections
are deliberately not identified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst)
open EagerDFS (World)
open EagerDFS.Destination NamedSpaces SpaceSemantics

theorem cursor_hit_has_first_answer (pattern : Atom) (rows : List Atom) (fuel : Nat)
    (entry : Nat × Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (found : (FirstQueryCursor.machine [] pattern).run fuel (0, rows) = ([], .finished (some entry))) :
    ∃ tail, query rows pattern (Effects.boolean true) = Effects.boolean true :: tail := by
  exact ConstantQuerySource.cursor_hit_has_first_answer pattern (Effects.boolean true)
    (.grounded (.bool true)) rows fuel entry found

theorem cursor_miss_has_no_answers (pattern : Atom) (rows : List Atom) (fuel : Nat)
    (missed : (FirstQueryCursor.machine [] pattern).run fuel (0, rows) = ([], .finished none)) :
    query rows pattern (Effects.boolean true) = [] := by
  exact ConstantQuerySource.cursor_miss_has_no_answers pattern (Effects.boolean true) rows fuel missed

theorem primitive_query (state : Effects.State) (handle : Handle) (rows : List Atom)
    (pattern : Atom) (snapshot : state.read handle = some rows) :
    StdLib.apply state "match" [Effects.handleValue handle, pattern, Effects.boolean true] =
      .ok (state, query rows pattern (Effects.boolean true)) := by
  exact ConstantQuerySource.primitive_query state handle rows pattern (Effects.boolean true) snapshot

theorem first_query_prefix {Context : Type} (policy : Policy) (program : Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (inside kept : List (CollectionWork Context)) (previousBoundary : Nat)
    (arguments : List Atom) (destination pattern : Atom) (handle : Handle) (rows : List Atom) (fuel : Nat)
    (entry : Nat × Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (environment afterEnvironment : Environment) (bindings : Equations)
    (frontier : scope.frontier = (control, context, origins) :: inside ++ kept)
    (atCall : control.goals = [.invoke "match" arguments destination, .commit, .restoreCommit previousBoundary])
    (boundary : control.cutBoundary = kept.length)
    (resolved : resolve control.bindings = some environment)
    (operands : arguments.map (read environment) = [Effects.handleValue handle, pattern, Effects.boolean true])
    (snapshot : world.state.read handle = some rows)
    (found : (FirstQueryCursor.machine [] pattern).run fuel (0, rows) = ([], .finished (some entry)))
    (refined : refine control.bindings (Effects.boolean true) destination = some bindings)
    (afterResolved : resolve bindings = some afterEnvironment) :
    let answer : CollectedAnswer := ⟨read afterEnvironment control.destination, bindings, origins ++ [0], []⟩
    let after : ScopedCursor Context := (allocator, ⟨world, EagerDFS.Scope.record scope kept answer :: parents⟩)
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run 5
      (allocator, ⟨world, scope :: parents⟩) =
      (if scope.caller.isNone then [answer] else [], .exhausted after) := by
  exact ConstantQuerySource.first_query_prefix policy program allocator world scope parents control context
    origins inside kept previousBoundary arguments destination pattern (Effects.boolean true) (.grounded (.bool true))
    handle rows fuel entry environment afterEnvironment bindings frontier atCall boundary resolved operands
    snapshot found refined afterResolved

theorem empty_query_keeps_outer_work {Context : Type} (policy : Policy) (program : Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (arguments : List Atom)
    (destination pattern : Atom) (older : List Goal) (handle : Handle) (rows : List Atom) (fuel : Nat)
    (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (operands : arguments.map (read environment) = [Effects.handleValue handle, pattern, Effects.boolean true])
    (snapshot : world.state.read handle = some rows)
    (missed : (FirstQueryCursor.machine [] pattern).run fuel (0, rows) = ([], .finished none)) :
    scopeStep policy program (allocator, ⟨world, scope :: parents⟩) =
      .silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩) := by
  exact ConstantQuerySource.empty_query_keeps_outer_work policy program allocator world scope parents control context
    origins pending arguments destination pattern (Effects.boolean true) older handle rows fuel environment
    frontier atCall resolved operands snapshot missed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQuerySource
