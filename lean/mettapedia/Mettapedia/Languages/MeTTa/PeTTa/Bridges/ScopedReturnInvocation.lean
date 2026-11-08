import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnScopes
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRawEntry

/-!
# Return obligations through actual primitive and equation invocation

The raw invocation port is reached only after the source-owned query/case
ports have declined. Its actual result occurrences or complete equation
frontier then retain the older return continuation. No callee's returned
values or successful execution are used as a source semantics oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnInvocation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS (World)
open EagerDFS.Destination
open ScopedReturnScopes

def ActionReturns {Context : Type} (arguments : Context → Atom)
    (action : Source.ScopeAction Allocator Context) : Prop :=
  ∀ state ∈ RefinementTransport.actionStates action, Stack arguments state.2.scopes

theorem silent_returns {Context : Type} {arguments : Context → Atom} (state : ScopedCursor Context)
    (valid : Stack arguments state.2.scopes) : ActionReturns arguments (.silent state) := by
  simpa only [ActionReturns, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using valid

theorem call_returns {Context : Type} {arguments : Context → Atom} (state : ScopedCursor Context)
    (request : ScopeBoundary) (valid : Stack arguments state.2.scopes) : ActionReturns arguments (.call request state) := by
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
    (valid : Stack inputs (scope :: parents)) : ActionReturns inputs action := by
  have tail (name : String) : ScopedReturnObligation.Pending (.var name) control.destination control.goals →
      ScopedReturnObligation.Pending (.var name) control.destination older := by
    intro returning
    exact ScopedReturnRawEntry.pending_raw_invocation_tail name control.destination
      (allocator, ⟨world, scope :: parents⟩) scope parents control context origins pending head arguments destination
      older environment rfl frontier atCall resolved returning noQuery noCase
  cases source with
  | parsed text value after parseHead input returned =>
      apply silent_returns
      apply valid.replace_active control context origins pending _ scope.collected frontier
      rintro ⟨name, holds⟩ work present
      have sameContext : work.2.1 = context := by
        obtain ⟨row, _member, rfl⟩ := List.mem_map.mp present
        rfl
      change ScopedReturnLocal.AliasHolds (inputs work.2.1) work.1
      rw [sameContext]
      exact ⟨name, ScopedReturnDispatch.primitive_choices_with_tail name _ control context origins destination older
        [value] holds (tail name) work present⟩
  | primitive state values ordinary known returned =>
      apply silent_returns
      apply valid.replace_active control context origins pending _ scope.collected frontier
      rintro ⟨name, holds⟩ work present
      have sameContext : work.2.1 = context := by
        obtain ⟨row, _member, rfl⟩ := List.mem_map.mp present
        rfl
      change ScopedReturnLocal.AliasHolds (inputs work.2.1) work.1
      rw [sameContext]
      exact ⟨name, ScopedReturnDispatch.primitive_choices_with_tail name _ control context origins destination older
        values holds (tail name) work present⟩
  | equations selected ordinary known notIO declared selectedRows =>
      apply silent_returns
      apply valid.replace_active control context origins pending _ scope.collected frontier
      rintro ⟨name, holds⟩ work present
      obtain ⟨choice, member, rfl⟩ := List.mem_map.mp present
      exact ⟨name, ScopedReturnDispatch.equation_frontier_with_tail name _
        (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) head
        (arguments.map (read environment)) destination older _ selected pending.length holds (tail name)
        selectedRows choice member⟩
  | parseFault | parseAllocation | parseArity | primitiveFault | unserved => exact call_returns _ _ valid

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnInvocation
