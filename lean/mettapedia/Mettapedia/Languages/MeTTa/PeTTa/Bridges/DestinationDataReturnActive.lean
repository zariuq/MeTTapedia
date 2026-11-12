import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnInvocation

/-!
# Actual active-scope preservation for compound returns

Every source frontier operation is covered, including arbitrary inner
collection results, committed sibling filtering and recursive clause entry.
The pure constructor-debt phase is consumed only by the actual local step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnActive

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS (World Scope)
open EagerDFS.Destination
open DestinationDataReturnScopes DestinationDataReturnInvocation

theorem active_preserves {Context : Type} (inputs : Context → Atom)
    {program : SpaceSemantics.Program} {allocator : Allocator} {world : World}
    {scope : CollectionScope Context} {parents : List (CollectionScope Context)}
    {control : Control} {context : Context} {origins : List Nat} {pending : List (CollectionWork Context)}
    {action : Source.ScopeAction Allocator Context}
    (source : Source.ActiveStep Source.FreshOperations.owned .eagerValue program allocator world scope parents
      control context origins pending action)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (noSequence : ScopedQuerySource.syntaxStep (allocator, ⟨world, scope :: parents⟩) = none)
    (noQuery : ScopedQuerySource.queryStep (allocator, ⟨world, scope :: parents⟩) = none)
    (noCase : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern
      (allocator, ⟨world, scope :: parents⟩) = none)
    (valid : Stack program inputs (scope :: parents)) : ActionReturns program inputs action := by
  cases source with
  | opening older atGoal =>
      apply silent_returns
      apply valid.replace_active control context origins pending [(_, context, origins)] scope.collected frontier
      rintro ⟨recipe, data, holds⟩ work member
      cases List.mem_singleton.mp member
      exact ⟨recipe, data, DestinationDataReturnDispatch.open_commit_return control older pending.length holds atGoal⟩
  | committing older younger kept atGoal partition boundary =>
      apply silent_returns
      apply valid.replace_head
      intro root work member
      subst parents
      have workGood := valid.root_work
      rcases List.mem_cons.mp member with rfl | retained
      · obtain ⟨recipe, data, holds⟩ := workGood (control, context, origins) (frontier ▸ List.mem_cons_self)
        exact ⟨recipe, data, DestinationDataReturnDispatch.commit_return control older holds atGoal⟩
      · apply workGood work
        rw [frontier, partition]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ retained)
  | invalidCommit => exact call_returns _ _ valid
  | next reached localStep =>
      apply silent_returns
      apply valid.replace_active control context origins pending [(reached.control, reached.context, origins)] scope.collected frontier
      intro holds work member
      cases List.mem_singleton.mp member
      change DestinationDataReturnState.AliasHolds program (inputs reached.context) reached.control
      rw [RefinementTransport.silent_context_preserved localStep]
      exact DestinationDataReturnState.alias_silent_preserves (inputs context) holds
        (ScopedReturnLocal.local_sequence_exclusion (allocator, ⟨world, scope :: parents⟩) scope parents control
          context origins pending rfl frontier noSequence) localStep
  | refused bindings reached localStep =>
      apply silent_returns
      exact valid.replace_active control context origins pending [] scope.collected frontier
        (by intro _ work member; cases member)
  | answered value bindings reached localStep =>
      have preserved := valid.replace_active control context origins pending []
        (scope.collected ++ [⟨value, bindings, origins, []⟩]) frontier (by intro _ work member; cases member)
      split <;> simpa only [ActionReturns, RefinementTransport.actionStates, List.mem_singleton,
        forall_eq, Scope.record, List.nil_append] using preserved
  | boundary => exact call_returns _ _ valid
  | invocation head arguments destination older environment action atCall resolved notPrint served =>
      exact invocation_preserves inputs served frontier atCall resolved noQuery noCase valid
  | queried space pattern body destination older environment rows selected atQuery resolved readRows selectedRows =>
      apply silent_returns
      apply valid.replace_active control context origins pending _ scope.collected frontier
      rintro ⟨recipe, data, holds⟩ work member
      obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
      exact ⟨recipe, data, DestinationDataReturnDispatch.query_selected_return
        (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) space pattern body destination older
        rows 0 selected holds atQuery selectedRows choice present⟩
  | queryFault => exact call_returns _ _ valid
  | collapsed expression destination older atGoal =>
      apply silent_returns
      apply valid.push
      · intro root work present
        subst parents
        exact valid.root_work work (frontier ▸ List.mem_cons_of_mem _ present)
      · intro root caller saved
        subst parents
        cases Option.some.inj saved
        obtain ⟨recipe, data, holds⟩ := valid.root_work (control, context, origins) (frontier ▸ List.mem_cons_self)
        exact ⟨recipe, data, DestinationDataReturnDispatch.collapse_saved_return data control expression destination older holds atGoal⟩
  | choice alternatives destination older atGoal =>
      apply silent_returns
      apply valid.replace_active control context origins pending _ scope.collected frontier
      rintro ⟨recipe, data, holds⟩ work present
      have sameContext : work.2.1 = context := by
        obtain ⟨row, _member, rfl⟩ := List.mem_map.mp present
        rfl
      change DestinationDataReturnState.AliasHolds program (inputs work.2.1) work.1
      rw [sameContext]
      exact ⟨recipe, data, DestinationDataReturnDispatch.superpose_choices_return data control context origins alternatives
        destination older holds atGoal work present⟩
  | empty destination older atGoal =>
      apply silent_returns
      exact valid.replace_active control context origins pending [] scope.collected frontier
        (by intro _ work member; cases member)

theorem collection_preserves {Context : Type} (inputs : Context → Atom) {program : SpaceSemantics.Program}
    {before after : ScopedCursor Context}
    (source : Source.CollectionReturn Source.FreshOperations.owned before after)
    (valid : Stack program inputs before.2.scopes) : Stack program inputs after.2.scopes := by
  cases source with
  | complete supply after world answers caller parent parents copied ready returned copies =>
      apply valid.resume caller rfl
      rintro ⟨recipe, data, holds⟩
      exact ⟨recipe, data, holds.prepend_equation _ _⟩

theorem scoped_preserves {Context : Type} (inputs : Context → Atom) {program : SpaceSemantics.Program}
    {before : ScopedCursor Context} {action : Source.ScopeAction Allocator Context}
    (source : Source.ScopedStep Source.FreshOperations.owned .eagerValue program before action)
    (noSequence : ScopedQuerySource.syntaxStep before = none)
    (noQuery : ScopedQuerySource.queryStep before = none)
    (noCase : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern before = none)
    (valid : Stack program inputs before.2.scopes) : ActionReturns program inputs action := by
  cases source with
  | active allocator world scope parents control context origins pending action frontier active =>
      exact active_preserves inputs active frontier noSequence noQuery noCase valid
  | finished => simpa only [ActionReturns, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using valid
  | collected source => exact silent_returns _ (collection_preserves inputs source valid)
  | associated | allocation => exact call_returns _ _ valid

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnActive
