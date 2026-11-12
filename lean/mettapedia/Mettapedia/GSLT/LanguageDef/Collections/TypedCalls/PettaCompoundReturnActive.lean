import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnSurface
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkDepth

/-!
# Focused source transitions retain computed compound obligations

Marked terminals are excluded from untyped publication by physical depth
and call order. Other actual source transitions retain their reached worlds,
constraints and complete generated frontiers through the shared mark update.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

theorem active_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    {program : SpaceSemantics.Program} {allocator : Allocator} {world : EagerDFS.World}
    {current : Scope User} {parents : List (Scope User)} {control : DControl} {context : Context User}
    {origins : List Nat} {pending : List (Work User)} {action : Source.ScopeAction Allocator (Context User)}
    (source : Source.ActiveStep Source.FreshOperations.owned .eagerValue program allocator world current parents
      control context origins pending action)
    (front : current.frontier = (control, context, origins) :: pending)
    (noSequence : Bridges.ScopedQuerySource.syntaxStep (allocator, ⟨world, current :: parents⟩) = none)
    (noQuery : Bridges.ScopedQuerySource.queryStep (allocator, ⟨world, current :: parents⟩) = none)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern
      (allocator, ⟨world, current :: parents⟩) = none)
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) (current :: parents))
    (sourceLane : PettaReturnMarkUpdate.frameActive (allocator, ⟨world, current :: parents⟩) = false)
    (unmarkedTerminal : control.goals = [] → mark = none) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks)
      (allocator, ⟨world, current :: parents⟩) (liftSource action) := by
  cases source with
  | opening older atGoal =>
      apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending [(_, context, origins)] mark pendingMarks callerMark parentMarks
        held rfl front (.inr (by intro tail same; rw [atGoal] at same; cases same)) _ _ _
      intro active
      apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (control, context, origins) [(_, context, origins)] mark
      · intro item member; cases List.mem_singleton.mp member; rfl
      · intro index marked item member
        cases List.mem_singleton.mp member
        exact PettaCompoundSelectedWork.opening control context origins (active index marked) older pending.length atGoal
  | committing older younger kept atGoal partition boundary =>
      exact commit_keeps _ current parents control context origins pending younger kept mark pendingMarks callerMark parentMarks
        older held rfl front atGoal partition sourceLane
  | invalidCommit => exact call_keeps _ _ _ held
  | next reached localStep =>
      apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending [(reached.control, reached.context, origins)] mark pendingMarks
        callerMark parentMarks held rfl front (.inr (PettaMarkedTransitions.silent_not_commit localStep)) _ _ _
      intro active
      apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (control, context, origins) [(reached.control, reached.context, origins)] mark
      · intro item member; cases List.mem_singleton.mp member
        exact congrArg (fun c => c.calls.length) (RefinementTransport.silent_context_preserved localStep)
      · intro index marked item member
        cases List.mem_singleton.mp member
        exact PettaCompoundSelectedWork.local_source origins localStep (active index marked)
          (Bridges.ScopedReturnLocal.local_sequence_exclusion (allocator, ⟨world, current :: parents⟩)
            current parents control context origins pending rfl front noSequence)
  | refused bindings reached localStep =>
      apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending [] mark pendingMarks callerMark parentMarks held rfl front
        (.inr (PettaMarkedTransitions.finish_not_commit localStep)) _ _ _
      intro active item member; cases member
  | answered value bindings reached localStep =>
      have terminal := ((Source.Step.returned_iff .eagerValue program _ reached value bindings).mp localStep).2.2.1
      have unmarked := unmarkedTerminal terminal
      subst mark
      have advanced := PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending [] none pendingMarks callerMark
        parentMarks held rfl front (.inr (PettaMarkedTransitions.finish_not_commit localStep))
        (by intro active item member; cases member) allocator reached.world
        (current.collected ++ [⟨value, bindings, origins, []⟩])
      split <;> simpa only [Preserves, PettaMarkedTransitions.Preserves, PettaOccurrenceBinding.retained, liftSource,
        EagerDFS.Scope.record, List.nil_append] using advanced
  | boundary => exact call_keeps _ _ _ held
  | invocation head arguments destination older environment action atCall resolved notPrint served =>
      exact invocation_keeps served front atCall resolved noQuery noCase mark pendingMarks callerMark parentMarks held
  | queried space pattern body destination older environment rows selected atQuery resolved readRows selectedRows =>
      apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks held rfl front
        (.inr (PettaMarkedTransitions.query_not_commit atQuery)) _ _ _
      intro active
      apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (control, context, origins) (selected.map fun choice => (choice.2, context, origins ++ [choice.1])) mark
      · intro item member; obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member; rfl
      · intro index marked item member
        obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
        exact PettaCompoundSelectedWork.query_choices (protectControl control (collectionSupport ⟨world, current :: parents⟩))
          context origins space pattern body destination older rows 0 selected
          (protected_control_marked control context origins _ active index marked) atQuery selectedRows choice present
  | queryFault => exact call_keeps _ _ _ held
  | collapsed expression destination older atGoal =>
      exact collapse_keeps _ current parents control context origins pending mark pendingMarks callerMark parentMarks
        expression destination older held rfl front atGoal _ rfl allocator world
  | choice alternatives destination older atGoal =>
      apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks held rfl front
        (.inr (PettaMarkedTransitions.evaluate_not_commit atGoal)) _ _ _
      intro active
      apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (control, context, origins) (superposeWork control context origins alternatives destination older) mark
      · intro item member; obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member; rfl
      · intro index marked
        exact PettaCompoundSelectedWork.superpose_choices control context origins alternatives destination older
          (active index marked) atGoal
  | empty destination older atGoal =>
      apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending [] mark pendingMarks callerMark parentMarks held rfl front
        (.inr (PettaMarkedTransitions.evaluate_not_commit atGoal)) _ _ _
      intro active item member; cases member

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
