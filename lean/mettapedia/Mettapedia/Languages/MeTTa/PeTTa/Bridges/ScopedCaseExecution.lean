import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryBinding

/-!
# Actual case source steps and their retained caller

The local case operations are connected to the existing owned scope driver.
The complete first-match evidence determines the selected record and source
body. Attaching older protected work changes neither the key producer's
fresh slot nor the ready selection decision.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS (World)
open EagerDFS.Destination
open EagerDFSStreaming.Scoped.ProtectedContinuation

theorem source_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atSource : control.goals = .evaluate (.expression [.symbol "case", key, .expression rows]) destination :: older)
    (parsed : Eval.readCases rows = some cases) :
    (ScopedQuerySource.ownedMachine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with frontier :=
        ({control with goals := [.evaluate key (.var (freshName control 0)),
          .invoke "case" [.var (freshName control 0), .expression rows] destination] ++ older},
          context, origins) :: pending} :: parents⟩)) := by
  simp only [ScopedQuerySource.ownedMachine, ScopedQuerySource.ownedStep,
    ScopedCaseSource.entered_key_once allocator world scope parents control context origins pending
      key destination rows cases older frontier atSource parsed]

theorem selected_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older : List Goal)
    (environment : Environment) (choice : ScopedCaseSelection.Choice)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atReady : control.goals = .invoke "case" [key, .expression rows] destination :: older)
    (resolved : resolve control.bindings = some environment) (parsed : Eval.readCases rows = some cases)
    (admitted : (finiteStructural (read environment key) &&
      cases.all (fun row => ScopedQuerySource.plainQueryPattern row.1)) = true)
    (selected : ScopedCaseSelection.Selection control.bindings key 0 cases (some choice)) :
    (ScopedQuerySource.ownedMachine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with frontier :=
        ({control with bindings := choice.bindings, goals := .evaluate choice.body destination :: older},
          context, origins ++ [choice.occurrence]) :: pending} :: parents⟩)) := by
  have entered := ScopedCaseSource.selected_body_entry ScopedQuerySource.plainQueryPattern allocator world
    scope parents control context origins pending key destination rows cases older environment choice
    frontier atReady resolved parsed admitted selected
  simp [ScopedQuerySource.ownedMachine, ScopedQuerySource.ownedStep,
    ScopedCaseSource.entryStep, frontier, atReady, entered]

theorem exhausted_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older : List Goal)
    (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atReady : control.goals = .invoke "case" [key, .expression rows] destination :: older)
    (resolved : resolve control.bindings = some environment) (parsed : Eval.readCases rows = some cases)
    (admitted : (finiteStructural (read environment key) &&
      cases.all (fun row => ScopedQuerySource.plainQueryPattern row.1)) = true)
    (exhausted : ScopedCaseSelection.Selection control.bindings key 0 cases none) :
    (ScopedQuerySource.ownedMachine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  have refused := ScopedCaseSource.exhausted_patterns_refuse_only_current ScopedQuerySource.plainQueryPattern
    allocator world scope parents control context origins pending key destination rows cases older environment
    frontier atReady resolved parsed admitted exhausted
  simp [ScopedQuerySource.ownedMachine, ScopedQuerySource.ownedStep,
    ScopedCaseSource.entryStep, frontier, atReady, refused]

theorem selected_entry_attach {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older suffix : List Goal)
    (environment : Environment) (choice : ScopedCaseSelection.Choice)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atReady : control.goals = .invoke "case" [key, .expression rows] destination :: older)
    (resolved : resolve control.bindings = some environment) (parsed : Eval.readCases rows = some cases)
    (admitted : (finiteStructural (read environment key) &&
      cases.all (fun row => ScopedQuerySource.plainQueryPattern row.1)) = true)
    (selected : ScopedCaseSelection.Selection control.bindings key 0 cases (some choice)) :
    (ScopedQuerySource.ownedMachine policy program).step (attachState suffix (allocator, ⟨world, scope :: parents⟩)) =
      some (.silent (attachState suffix (allocator, ⟨world, {scope with frontier :=
        ({control with bindings := choice.bindings, goals := .evaluate choice.body destination :: older},
          context, origins ++ [choice.occurrence]) :: pending} :: parents⟩))) := by
  have actual := selected_entry policy program allocator world (attachScope suffix scope) parents
    (attach suffix control) context origins (pending.map (attachWork suffix)) key destination rows cases
    (older.map (shift suffix.length) ++ suffix) environment choice
    (by simp only [attachScope, frontier, List.map_cons, attachWork])
    (by simp only [attach, atReady, List.map_cons, shift, List.cons_append])
    resolved parsed admitted selected
  simpa only [attachState, attachScope, attachWork, attach, List.map_cons, shift, List.cons_append] using actual

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseExecution
