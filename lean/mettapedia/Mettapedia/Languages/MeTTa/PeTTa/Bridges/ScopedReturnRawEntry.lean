import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnDispatch

/-!
# Raw invocation is reached only after the owned surface ports decline

A return-bearing query template is not a scalar-data fusion. Case selection
likewise owns its ready arm table. These concrete dispatch facts prevent raw
primitive calls from being mistaken for execution of an unevaluated body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRawEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ScopedReturnSyntax (Returns)
open ScopedReturnObligation (Pending AtHead)

theorem variable_return_is_not_scalar (name : String) {body : Atom} (returns : Returns (.var name) body) :
    ConstantQuerySource.isScalar body = false := by cases returns <;> rfl

theorem query_return_has_handler {Context : Type} (name : String) (source : ScopedCursor Context)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern body destination : Atom) (older : List Goal) (environment : Environment)
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (resolved : resolve control.bindings = some environment) (returns : Returns (.var name) body) :
    ScopedQuerySource.queryStep source ≠ none := by
  simp only [ScopedQuerySource.queryStep, scopes, frontier, atGoal, resolved,
    ScopedQuerySource.fused, variable_return_is_not_scalar name returns, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  repeat' first
    | simp
    | (split <;> try dsimp only [bind, Option.bind])

theorem case_return_has_handler {Context : Type} (source : ScopedCursor Context)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older : List Goal)
    (environment : Environment) (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .invoke "case" [key, .expression rows] destination :: older)
    (resolved : resolve control.bindings = some environment) (parsed : Eval.readCases rows = some cases) :
    ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern source ≠ none := by
  simp only [ScopedCaseSource.readyStep, scopes, frontier, atGoal, resolved, parsed]
  repeat' first
    | simp
    | (split <;> try dsimp only [bind, Option.bind])

/-- Every raw successful invocation has a genuine pending older return.
The exceptions are not excluded from the language: their owned source ports
must have handled them, so they cannot be this raw dispatch step. -/
theorem pending_raw_invocation_tail {Context : Type} (name : String) (target : Atom)
    (source : ScopedCursor Context) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (environment : Environment)
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (returning : Pending (.var name) target control.goals)
    (noQuery : ScopedQuerySource.queryStep source = none)
    (noCase : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern source = none) :
    Pending (.var name) target older := by
  rcases returning.head_or_tail _ _ atGoal with marked | tail
  · unfold AtHead at marked
    split at marked <;> try contradiction
    · rename_i space pattern body result shape
      have atQuery := atGoal.trans (congrArg (fun goal => goal :: older) shape)
      exact False.elim ((query_return_has_handler name source scope parents control context origins pending
        space pattern body result older environment scopes frontier atQuery resolved marked.2) noQuery)
    · rename_i key rows result shape
      obtain ⟨_, cases, parsed, _⟩ := marked
      have atCase := atGoal.trans (congrArg (fun goal => goal :: older) shape)
      exact False.elim ((case_return_has_handler source scope parents control context origins pending
        key result rows cases older environment scopes frontier atCase resolved parsed) noCase)
  · exact tail

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRawEntry
