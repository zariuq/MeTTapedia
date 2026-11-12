import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkInvocation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkScope

/-!
# Deterministic marks through the focused source dispatcher

The actual source rules supply the generated work and reached state. A
marked terminal cannot use the source's untyped publication rule: typed
return dispatch must handle it first. Collection children keep independent
work while the saved caller carries the outer obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks Stack)

theorem silent_not_commit {User : Type} {program : SpaceSemantics.Program}
    {before after : Cursor (Context User)}
    (source : Source.Step .eagerValue program before (.silent after)) :
    ∀ older, before.control.goals ≠ .commit :: older := PettaMarkedTransitions.silent_not_commit source

theorem finish_not_commit {User : Type} {program : SpaceSemantics.Program}
    {before after : Cursor (Context User)} {result : Result}
    (source : Source.Step .eagerValue program before (.finish (result, after))) :
    ∀ older, before.control.goals ≠ .commit :: older := PettaMarkedTransitions.finish_not_commit source

theorem query_not_commit {control : DControl} {space pattern body destination : Atom}
    {older : List EagerDFS.Destination.Goal}
    (scheduled : control.goals = .query space pattern body destination :: older) :
    ∀ tail, control.goals ≠ .commit :: tail := PettaMarkedTransitions.query_not_commit scheduled

theorem active_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    {program : SpaceSemantics.Program} {allocator : Allocator} {world : EagerDFS.World}
    {current : Scope User} {parents : List (Scope User)} {control : DControl} {context : Context User}
    {origins : List Nat} {pending : List (Work User)}
    {action : Source.ScopeAction Allocator (Context User)}
    (source : Source.ActiveStep Source.FreshOperations.owned .eagerValue program allocator world current parents
      control context origins pending action)
    (front : current.frontier = (control, context, origins) :: pending)
    (noSequence : Bridges.ScopedQuerySource.syntaxStep (allocator, ⟨world, current :: parents⟩) = none)
    (noQuery : Bridges.ScopedQuerySource.queryStep (allocator, ⟨world, current :: parents⟩) = none)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern
      (allocator, ⟨world, current :: parents⟩) = none)
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) (current :: parents))
    (sourceLane : frameActive (allocator, ⟨world, current :: parents⟩) = false)
    (unmarkedTerminal : control.goals = [] → mark = none) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks)
      (allocator, ⟨world, current :: parents⟩) (liftSource action) := by
  cases source with
  | opening older atGoal =>
      apply installed_scope_keeps _ current parents (control, context, origins) pending [(_, context, origins)]
        mark pendingMarks callerMark parentMarks held rfl front
        (.inr (by intro tail same; rw [atGoal] at same; cases same)) _ _ _
      intro active
      apply same_count_generated (control, context, origins) _ mark
      · intro item member
        cases List.mem_singleton.mp member
        rfl
      · intro index marked item member
        cases List.mem_singleton.mp member
        exact PettaSelectedReturnWork.opening control context origins (active index marked) older pending.length atGoal
  | committing older younger kept atGoal partition boundary =>
      exact commit_keeps _ current parents control context origins pending younger kept mark pendingMarks callerMark parentMarks
        older held rfl front atGoal partition sourceLane
  | invalidCommit => exact call_keeps _ _ _ held
  | next reached localStep =>
      apply installed_scope_keeps _ current parents (control, context, origins) pending [(reached.control, reached.context, origins)]
        mark pendingMarks callerMark parentMarks held rfl front (.inr (silent_not_commit localStep)) _ _ _
      intro active
      apply same_count_generated (control, context, origins) _ mark
      · intro item member
        cases List.mem_singleton.mp member
        exact congrArg (fun c => c.calls.length) (RefinementTransport.silent_context_preserved localStep)
      · intro index marked item member
        cases List.mem_singleton.mp member
        exact PettaSelectedReturnWork.local_source origins localStep (active index marked)
          (Bridges.ScopedReturnLocal.local_sequence_exclusion (allocator, ⟨world, current :: parents⟩)
            current parents control context origins pending rfl front noSequence)
  | refused bindings reached localStep =>
      apply installed_scope_keeps _ current parents (control, context, origins) pending []
        mark pendingMarks callerMark parentMarks held rfl front (.inr (finish_not_commit localStep)) _ _ _
      intro _ item member
      cases member
  | answered value bindings reached localStep =>
      have terminal := ((Source.Step.returned_iff .eagerValue program _ reached value bindings).mp localStep).2.2.1
      have unmarked := unmarkedTerminal terminal
      subst mark
      have advanced := installed_scope_keeps (saved := saved) (argument := argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending []
        none pendingMarks callerMark parentMarks held rfl front (.inr (finish_not_commit localStep))
        (by intro _ item member; cases member) allocator reached.world
        (current.collected ++ [⟨value, bindings, origins, []⟩])
      split <;> simpa only [Preserves, PettaMarkedTransitions.Preserves, PettaOccurrenceBinding.retained,
        liftSource, EagerDFS.Scope.record, List.nil_append]
        using advanced
  | boundary => exact call_keeps _ _ _ held
  | invocation head arguments destination older environment action atCall resolved notPrint served =>
      exact invocation_keeps served front atCall resolved noQuery noCase mark pendingMarks callerMark parentMarks held
  | queried space pattern body destination older environment rows selected atQuery resolved readRows selectedRows =>
      apply installed_scope_keeps _ current parents (control, context, origins) pending _
        mark pendingMarks callerMark parentMarks held rfl front (.inr (query_not_commit atQuery)) _ _ _
      intro active
      apply same_count_generated (control, context, origins) _ mark
      · intro item member
        obtain ⟨choice, _present, rfl⟩ := List.mem_map.mp member
        rfl
      · intro index marked item member
        obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
        exact PettaSelectedReturnWork.query_choices
          (protectControl control (collectionSupport ⟨world, current :: parents⟩)) context origins space pattern body destination
          older rows 0 selected (protected_control_marked control context origins _ active index marked)
          atQuery selectedRows choice present
  | queryFault => exact call_keeps _ _ _ held
  | collapsed expression destination older atGoal =>
      exact collapse_keeps _ current parents control context origins pending mark pendingMarks callerMark parentMarks
        expression destination older held rfl front atGoal _ rfl allocator world
  | choice alternatives destination older atGoal =>
      apply installed_scope_keeps _ current parents (control, context, origins) pending _
        mark pendingMarks callerMark parentMarks held rfl front (.inr (evaluate_not_commit atGoal)) _ _ _
      intro active
      apply same_count_generated (control, context, origins) _ mark
      · intro item member
        obtain ⟨entry, _present, rfl⟩ := List.mem_map.mp member
        rfl
      · intro index marked
        exact PettaSelectedReturnWork.superpose_choices control context origins alternatives destination older (active index marked) atGoal
  | empty destination older atGoal =>
      apply installed_scope_keeps _ current parents (control, context, origins) pending []
        mark pendingMarks callerMark parentMarks held rfl front (.inr (evaluate_not_commit atGoal)) _ _ _
      intro _ item member
      cases member

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
