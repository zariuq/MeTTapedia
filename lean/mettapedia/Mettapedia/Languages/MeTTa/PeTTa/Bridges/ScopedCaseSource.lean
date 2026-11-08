import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseSelection

/-!
# Case source entry and its ready selection boundary

The key is an ordinary source producer. Each delivered key reaches the
existing invocation goal with the authored arm table retained as data.
Selection commits to a pattern before scheduling its original body. These
two local operations are adapters for the existing scope owner, not drivers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination

abbrev Action (Context : Type) :=
  Transition (ScopedCursor Context) CollectedAnswer (ScopedCursor Context) ScopeBoundary

def entryStep {Context : Type} (source : ScopedCursor Context) : Option (Action Context) := do
  let scope :: parents := source.2.scopes | none
  let (control, context, origins) :: pending := scope.frontier | none
  let .evaluate (.expression [.symbol "case", key, .expression rows]) destination :: older := control.goals | none
  let fallback := .call (.branch (.invoke "case" [key, .expression rows] destination)) source
  match Eval.readCases rows with
  | none => some fallback
  | some _ =>
      let slot := Atom.var (freshName control 0)
      let next := {control with goals :=
        [.evaluate key slot, .invoke "case" [slot, .expression rows] destination] ++ older}
      some (.silent (source.1, ⟨source.2.world,
        {scope with frontier := (next, context, origins) :: pending} :: parents⟩))

/-- Pattern admission is supplied by the existing source-profile checker;
the choice itself is always the same actual finite-term refinement scan. -/
def readyStep {Context : Type} (admitPattern : Atom → Bool)
    (source : ScopedCursor Context) : Option (Action Context) := do
  let scope :: parents := source.2.scopes | none
  let (control, context, origins) :: pending := scope.frontier | none
  let .invoke "case" [key, .expression rows] destination :: older := control.goals | none
  let fallback := .call (.branch (.invoke "case" [key, .expression rows] destination)) source
  let environment ← resolve control.bindings
  match Eval.readCases rows with
  | none => some fallback
  | some cases =>
      if finiteStructural (read environment key) && cases.all (fun row => admitPattern row.1) then
        let work := match ScopedCaseSelection.select control.bindings key 0 cases with
          | none => []
          | some choice =>
              [({control with bindings := choice.bindings, goals := .evaluate choice.body destination :: older},
                context, origins ++ [choice.occurrence])]
        some (.silent (source.1, ⟨source.2.world,
          {scope with frontier := work ++ pending} :: parents⟩))
      else some fallback

theorem entered_key_once {Context : Type} (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atSource : control.goals = .evaluate (.expression [.symbol "case", key, .expression rows]) destination :: older)
    (parsed : Eval.readCases rows = some cases) :
    entryStep (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with frontier :=
        ({control with goals := [.evaluate key (.var (freshName control 0)),
          .invoke "case" [.var (freshName control 0), .expression rows] destination] ++ older},
          context, origins) :: pending} :: parents⟩)) := by
  simp [entryStep, frontier, atSource, parsed]

theorem selected_body_entry {Context : Type} (admitPattern : Atom → Bool)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older : List Goal)
    (environment : Environment) (choice : ScopedCaseSelection.Choice)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atReady : control.goals = .invoke "case" [key, .expression rows] destination :: older)
    (resolved : resolve control.bindings = some environment) (parsed : Eval.readCases rows = some cases)
    (admitted : (finiteStructural (read environment key) && cases.all (fun row => admitPattern row.1)) = true)
    (selected : ScopedCaseSelection.Selection control.bindings key 0 cases (some choice)) :
    readyStep admitPattern (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with frontier :=
        ({control with bindings := choice.bindings, goals := .evaluate choice.body destination :: older},
          context, origins ++ [choice.occurrence]) :: pending} :: parents⟩)) := by
  simp [readyStep, frontier, atReady, resolved, parsed, admitted, selected.execution]

theorem exhausted_patterns_refuse_only_current {Context : Type} (admitPattern : Atom → Bool)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older : List Goal)
    (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atReady : control.goals = .invoke "case" [key, .expression rows] destination :: older)
    (resolved : resolve control.bindings = some environment) (parsed : Eval.readCases rows = some cases)
    (admitted : (finiteStructural (read environment key) && cases.all (fun row => admitPattern row.1)) = true)
    (exhausted : ScopedCaseSelection.Selection control.bindings key 0 cases none) :
    readyStep admitPattern (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  simp [readyStep, frontier, atReady, resolved, parsed, admitted, exhausted.execution]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseSource
