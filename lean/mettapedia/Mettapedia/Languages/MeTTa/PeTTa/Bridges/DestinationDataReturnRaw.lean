import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnDispatch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRawEntry

/-!
# Scalar query fusion and compound return obligations

The owned query handler deliberately leaves literal scalar templates to the
ordinary source primitive. Such a template is not arbitrary executed code:
every actual query result is that same scalar. This case must be proved,
not removed by requiring every return recipe to be a variable or expression.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRaw

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ScopedReturnSyntax (Returns)
open ScopedReturnObligation (Pending AtHead)

theorem scalar_return_is_recipe {recipe body : Atom} (returns : Returns recipe body)
    (scalar : ConstantQuerySource.Scalar body) : body = recipe := by
  cases returns <;> cases scalar <;> rfl

theorem unhandled_query_is_scalar {Context : Type} (source : ScopedCursor Context)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern body destination : Atom) (older : List Goal) (environment : Environment)
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (noQuery : ScopedQuerySource.queryStep source = none) : ConstantQuerySource.isScalar body = true := by
  simp only [ScopedQuerySource.queryStep, scopes, frontier, atGoal, resolved] at noQuery
  dsimp only [bind, Option.bind] at noQuery
  split at noQuery
  · cases noQuery
  · split at noQuery
    · split at noQuery
      · exact (Bool.and_eq_true_iff.mp (by assumption : ScopedQuerySource.fused (read environment pattern) body = true)).2
      · split at noQuery <;> cases noQuery
    · cases noQuery

theorem primitive_scalar_values (before after : Effects.State) (space pattern payload : Atom)
    (values : List Atom) (scalar : ConstantQuerySource.Scalar payload)
    (returned : StdLib.apply before "match" [space, pattern, payload] = .ok (after, values)) :
    ∀ value ∈ values, value = payload := by
  change (match Effects.readHandle space >>= before.read with
    | some rows => Except.ok (before, SpaceSemantics.query rows pattern payload)
    | none => Except.error Effects.Fault.invalidSpace) = Except.ok (after, values) at returned
  split at returned
  · rename_i rows snapshot
    have answers := (Prod.mk.inj (Except.ok.inj returned)).2
    intro value member
    rw [← answers] at member
    obtain ⟨row, present, bindings, matched, substituted⟩ := SpaceSemantics.query_sound member
    exact substituted.symm.trans (scalar.subst bindings)
  · cases returned

/-- Non-query source invocations cannot own a return at their head. Ready
case selection is handled by its real owner before this raw phase. -/
theorem nonquery_invocation_tail {Context : Type} (recipe target : Atom)
    (source : ScopedCursor Context) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (environment : Environment)
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment) (notQuery : head ≠ "match")
    (returning : Pending recipe target control.goals)
    (noCase : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern source = none) :
    Pending recipe target older := by
  rcases returning.head_or_tail _ _ atGoal with marked | tail
  · unfold AtHead at marked
    split at marked <;> try contradiction
    · rename_i space pattern body result shape
      exact (notQuery (by cases shape; rfl)).elim
    · rename_i key rows result shape
      obtain ⟨_, cases, parsed, _⟩ := marked
      have atCase := atGoal.trans (congrArg (fun goal => goal :: older) shape)
      exact ((ScopedReturnRawEntry.case_return_has_handler source scope parents control context origins pending
        key result rows cases older environment scopes frontier atCase resolved parsed) noCase).elim
  · exact tail

/-- Every actual primitive result retains the authored return, including the
scalar-query head case where the return is delivered by the primitive itself. -/
theorem primitive_return_pending {Context : Type} (recipe target : Atom)
    (source : ScopedCursor Context) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (environment : Environment)
    (state : Effects.State) (values : List Atom)
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (returning : Pending recipe target control.goals)
    (noQuery : ScopedQuerySource.queryStep source = none)
    (noCase : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern source = none)
    (returned : StdLib.apply source.2.world.state head (arguments.map (read environment)) = .ok (state, values)) :
    ∀ value ∈ values, Pending recipe target (.equate value destination :: older) := by
  rcases returning.head_or_tail _ _ atGoal with marked | tail
  · unfold AtHead at marked
    split at marked <;> try contradiction
    · rename_i space pattern body result shape
      have atQuery := atGoal.trans (congrArg (fun goal => goal :: older) shape)
      have scalar := (ConstantQuerySource.isScalar_iff body).mp
        (unhandled_query_is_scalar source scope parents control context origins pending space pattern body result
          older environment scopes frontier atQuery resolved noQuery)
      have same := scalar_return_is_recipe marked.2 scalar
      cases shape
      have operands : [space, pattern, body].map (read environment) =
          [read environment space, read environment pattern, body] := by
        simp only [List.map_cons, List.map_nil, scalar.read environment]
      rw [operands] at returned
      intro value present
      have delivered := primitive_scalar_values _ state _ _ body values scalar returned value present
      rw [← marked.1, delivered, same]
      exact .equation older
    · rename_i key rows result shape
      obtain ⟨_, cases, parsed, _⟩ := marked
      have atCase := atGoal.trans (congrArg (fun goal => goal :: older) shape)
      exact ((ScopedReturnRawEntry.case_return_has_handler source scope parents control context origins pending
        key result rows cases older environment scopes frontier atCase resolved parsed) noCase).elim
  · exact fun value _present => tail.prepend_equation value destination

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRaw
