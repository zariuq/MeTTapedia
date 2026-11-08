import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceInvocation

/-! Source scopes preserve active or suspended typed return obligations. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceActive

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames
open PettaCallerReturnSourceInvocation

theorem active_preserves {User : Type} (inputs : User → Atom) {program : SpaceSemantics.Program}
    {allocator : Allocator} {world : EagerDFS.World} {current : Scope User} {parents : List (Scope User)}
    {control : DControl} {context : Context User} {origins : List Nat} {pending : List (Work User)}
    {action : Source.ScopeAction Allocator (Context User)}
    (source : Source.ActiveStep Source.FreshOperations.owned .eagerValue program allocator world current parents
      control context origins pending action)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (noSequence : Bridges.ScopedQuerySource.syntaxStep (allocator, ⟨world, current :: parents⟩) = none)
    (noQuery : Bridges.ScopedQuerySource.queryStep (allocator, ⟨world, current :: parents⟩) = none)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern
      (allocator, ⟨world, current :: parents⟩) = none)
    (held : PettaCallerReturnView.Holds inputs (allocator, ⟨world, current :: parents⟩)) : Preserves inputs action := by
  cases source with
  | opening older atGoal =>
      apply silent_preserves
      apply PettaCallerReturnView.replace_active inputs _ current parents control context origins pending
        [(_, context, origins)] current.collected allocator world held rfl frontier
      intro captured item member
      cases List.mem_singleton.mp member
      exact PettaCallerReturnSourceChoices.opening captured older pending.length atGoal
  | committing older younger kept atGoal partition boundary =>
      apply silent_preserves
      apply PettaCallerReturnView.replace_root inputs _ current parents _ current.collected allocator world held rfl
      intro root item member
      subst parents
      have prior := PettaCallerReturnView.root_work inputs _ current rfl held
      rcases List.mem_cons.mp member with rfl | retained
      · exact PettaCallerReturnSourceChoices.committing
          (prior (control, context, origins) (frontier ▸ List.mem_cons_self)) older atGoal
      · apply prior item
        rw [frontier, partition]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ retained)
  | invalidCommit => exact call_preserves _ _ held
  | next reached localStep =>
      apply silent_preserves
      apply PettaCallerReturnView.replace_active inputs _ current parents control context origins pending
        [(reached.control, reached.context, origins)] current.collected allocator reached.world held rfl frontier
      intro captured item member
      cases List.mem_singleton.mp member
      exact PettaCallerReturnSourceChoices.local_step inputs localStep captured
        (Bridges.ScopedReturnLocal.local_sequence_exclusion (allocator, ⟨world, current :: parents⟩) current parents
          control context origins pending rfl frontier noSequence)
  | refused bindings reached localStep =>
      apply silent_preserves
      exact PettaCallerReturnView.replace_active inputs _ current parents control context origins pending [] current.collected
        allocator reached.world held rfl frontier (by intro _ item member; cases member)
  | answered value bindings reached localStep =>
      have advanced := PettaCallerReturnView.replace_active inputs _ current parents control context origins pending []
        (current.collected ++ [⟨value, bindings, origins, []⟩]) allocator reached.world held rfl frontier
        (by intro _ item member; cases member)
      split <;> simpa only [Preserves, RefinementTransport.actionStates, List.mem_singleton,
        forall_eq, EagerDFS.Scope.record, List.nil_append] using advanced
  | boundary => exact call_preserves _ _ held
  | invocation head arguments destination older environment action atCall resolved notPrint served =>
      exact invocation_preserves inputs served frontier atCall resolved noQuery noCase held
  | queried space pattern body destination older environment rows selected atQuery resolved readRows selectedRows =>
      apply silent_preserves
      apply PettaCallerReturnView.replace_active inputs _ current parents control context origins pending _ current.collected
        allocator world held rfl frontier
      intro captured item member
      obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
      exact PettaCallerReturnSourceChoices.query_frontier inputs
        (protectControl control (collectionSupport ⟨world, current :: parents⟩)) context space pattern body destination
        older rows 0 selected (captured.protect_control _) atQuery selectedRows choice present
  | queryFault => exact call_preserves _ _ held
  | collapsed expression destination older atGoal =>
      apply silent_preserves
      apply PettaCallerReturnView.push_scope inputs _ current parents _ pending allocator world held rfl
      · intro root item member
        subst parents
        exact PettaCallerReturnView.root_work inputs _ current rfl held item (frontier ▸ List.mem_cons_of_mem _ member)
      · intro root saved atCaller
        subst parents
        cases Option.some.inj atCaller
        exact PettaCallerReturnSourceChoices.collapse_caller
          (PettaCallerReturnView.root_work inputs _ current rfl held (control, context, origins) (frontier ▸ List.mem_cons_self))
          expression destination older atGoal
  | choice alternatives destination older atGoal =>
      apply silent_preserves
      apply PettaCallerReturnView.replace_active inputs _ current parents control context origins pending _ current.collected
        allocator world held rfl frontier
      intro captured
      exact PettaCallerReturnSourceChoices.superpose_frontier inputs control context origins alternatives destination older captured atGoal
  | empty destination older atGoal =>
      apply silent_preserves
      exact PettaCallerReturnView.replace_active inputs _ current parents control context origins pending [] current.collected
        allocator world held rfl frontier (by intro _ item member; cases member)

theorem collection_preserves {User : Type} (inputs : User → Atom) {before after : State User}
    (source : Source.CollectionReturn Source.FreshOperations.owned before after)
    (held : PettaCallerReturnView.Holds inputs before) : PettaCallerReturnView.Holds inputs after := by
  cases source with
  | complete supply after world answers saved parent parents copied ready returned copies =>
      apply PettaCallerReturnView.resume_scope inputs _ _ parent parents saved _ after world held rfl rfl
      intro captured
      exact PettaCallerReturnSourceChoices.collection_copies inputs copied saved captured

theorem scoped_preserves {User : Type} (inputs : User → Atom) {program : SpaceSemantics.Program}
    {before : State User} {action : Source.ScopeAction Allocator (Context User)}
    (source : Source.ScopedStep Source.FreshOperations.owned .eagerValue program before action)
    (noSequence : Bridges.ScopedQuerySource.syntaxStep before = none)
    (noQuery : Bridges.ScopedQuerySource.queryStep before = none)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern before = none)
    (held : PettaCallerReturnView.Holds inputs before) : Preserves inputs action := by
  cases source with
  | active allocator world current parents control context origins pending action frontier active =>
      exact active_preserves inputs active frontier noSequence noQuery noCase held
  | finished => simpa only [Preserves, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using held
  | collected source => exact silent_preserves _ (collection_preserves inputs source held)
  | associated | allocation => exact call_preserves _ _ held

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceActive
