import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnScopes

/-!
# Compound returns through actual raw source invocation

Primitive values and complete clause frontiers are the existing source
operation's results. Scalar query fusion is included; arbitrary callee body
success, output equality and native admission are not assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnInvocation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS (World)
open EagerDFS.Destination
open DestinationDataReturnScopes

def ActionReturns {Context : Type} (program : SpaceSemantics.Program) (arguments : Context → Atom)
    (action : Source.ScopeAction Allocator Context) : Prop :=
  ∀ state ∈ RefinementTransport.actionStates action, Stack program arguments state.2.scopes

theorem silent_returns {Context : Type} {program : SpaceSemantics.Program} {arguments : Context → Atom}
    (state : ScopedCursor Context) (valid : Stack program arguments state.2.scopes) :
    ActionReturns program arguments (.silent state) := by
  simpa only [ActionReturns, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using valid

theorem call_returns {Context : Type} {program : SpaceSemantics.Program} {arguments : Context → Atom}
    (state : ScopedCursor Context) (request : ScopeBoundary) (valid : Stack program arguments state.2.scopes) :
    ActionReturns program arguments (.call request state) := by
  simpa only [ActionReturns, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using valid

theorem invocation_preserves {Context : Type} (inputs : Context → Atom)
    {program : SpaceSemantics.Program} {allocator : Allocator} {world : World}
    {scope : CollectionScope Context} {parents : List (CollectionScope Context)}
    {control : Control} {context : Context} {origins : List Nat} {pending : List (CollectionWork Context)}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {environment : Environment} {action : Source.ScopeAction Allocator Context}
    (source : Source.Invocation Source.FreshOperations.owned program allocator world scope parents control context
      origins pending head arguments destination older environment action)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (noQuery : ScopedQuerySource.queryStep (allocator, ⟨world, scope :: parents⟩) = none)
    (noCase : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern
      (allocator, ⟨world, scope :: parents⟩) = none)
    (valid : Stack program inputs (scope :: parents)) : ActionReturns program inputs action := by
  have tail (recipe : Atom) (notQuery : head ≠ "match") :
      ScopedReturnObligation.Pending recipe control.destination control.goals →
      ScopedReturnObligation.Pending recipe control.destination older := by
    intro returning
    exact DestinationDataReturnRaw.nonquery_invocation_tail recipe control.destination
      (allocator, ⟨world, scope :: parents⟩) scope parents control context origins pending head arguments destination
      older environment rfl frontier atCall resolved notQuery returning noCase
  cases source with
  | parsed text value after parseHead input returned =>
      apply silent_returns
      apply valid.replace_active control context origins pending _ scope.collected frontier
      rintro ⟨recipe, data, holds⟩ work present
      have sameContext : work.2.1 = context := by
        obtain ⟨row, _member, rfl⟩ := List.mem_map.mp present
        rfl
      change DestinationDataReturnState.AliasHolds program (inputs work.2.1) work.1
      rw [sameContext]
      exact ⟨recipe, data, DestinationDataReturnDispatch.primitive_choices_with_tail control context origins head
        arguments destination older [value] holds atCall (tail recipe (by simp [parseHead])) work present⟩
  | primitive state values ordinary known returned =>
      apply silent_returns
      apply valid.replace_active control context origins pending _ scope.collected frontier
      rintro ⟨recipe, data, holds⟩ work present
      obtain ⟨⟨value, occurrence⟩, member, rfl⟩ := List.mem_map.mp present
      refine ⟨recipe, data, ?_⟩
      apply DestinationDataReturnDispatch.nondata_transition
        (after := {control with goals := .equate value destination :: older})
        holds atCall (by intro impossible; cases impossible) (fun _ solved => solved) rfl
      intro returning
      exact DestinationDataReturnRaw.primitive_return_pending recipe control.destination
        (allocator, ⟨world, scope :: parents⟩) scope parents control context origins pending head arguments destination
        older environment state values rfl frontier atCall resolved returning noQuery noCase returned value
        (List.fst_mem_of_mem_zipIdx member)
  | equations selected ordinary known notIO declared selectedRows =>
      apply silent_returns
      apply valid.replace_active control context origins pending _ scope.collected frontier
      rintro ⟨recipe, data, holds⟩ work present
      obtain ⟨choice, member, rfl⟩ := List.mem_map.mp present
      have notQuery : head ≠ "match" := by
        intro same
        rw [same] at known
        cases known
      exact ⟨recipe, data, DestinationDataReturnDispatch.equation_frontier_with_tail
        (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) head
        (arguments.map (read environment)) destination older _ selected pending.length holds ⟨arguments, atCall⟩
        (tail recipe notQuery) selectedRows choice member⟩
  | parseFault | parseAllocation | parseArity | primitiveFault | unserved => exact call_returns _ _ valid

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnInvocation
