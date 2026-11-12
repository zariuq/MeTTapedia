import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedSources
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes

/-!
# Actual source invocations preserve computed compound-return marks

The source supplies parsed values, primitive replies and complete clause
frontiers. Scalar-query delivery uses its actual answers; it is not weakened
to a suffix-only return. Missing services retain the actual source state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

theorem protected_control_marked {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {mark : Option Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (boundary : Finset String) (held : WorkMarked program saved argument mark (control, context, origins)) :
    WorkMarked program saved argument mark (protectControl control boundary, context, origins) :=
  fun index marked => PettaCompoundSelectedWork.protect_control control context origins boundary (held index marked)

theorem invocation_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    {program : SpaceSemantics.Program} {allocator : Allocator} {world : EagerDFS.World}
    {current : Scope User} {parents : List (Scope User)} {control : DControl} {context : Context User}
    {origins : List Nat} {pending : List (Work User)} {head : String} {arguments : List Atom}
    {destination : Atom} {older : List EagerDFS.Destination.Goal} {environment : Environment}
    {action : Source.ScopeAction Allocator (Context User)}
    (source : Source.Invocation Source.FreshOperations.owned program allocator world current parents control context origins pending
      head arguments destination older environment action)
    (front : current.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (noQuery : Bridges.ScopedQuerySource.queryStep (allocator, ⟨world, current :: parents⟩) = none)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern
      (allocator, ⟨world, current :: parents⟩) = none)
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) (current :: parents)) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks)
      (allocator, ⟨world, current :: parents⟩) (liftSource action) := by
  have tail (recipe : Atom) (notQuery : head ≠ "match") :
      Bridges.ScopedReturnObligation.Pending recipe control.destination control.goals →
        Bridges.ScopedReturnObligation.Pending recipe control.destination older := by
    intro returning
    exact Bridges.DestinationDataReturnRaw.nonquery_invocation_tail recipe control.destination
      (allocator, ⟨world, current :: parents⟩) current parents control context origins pending head arguments destination older
      environment rfl front atCall resolved notQuery returning noCase
  have notCommit : ∀ other, control.goals ≠ .commit :: other := by
    intro other same
    rw [atCall] at same
    cases same
  cases source with
  | parsed text value after parseHead input returned =>
      apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending _ mark pendingMarks
        callerMark parentMarks held rfl front (.inr notCommit) _ _ _
      intro active
      apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (control, context, origins) (primitiveWork control context origins destination older [value]) mark
      · intro item member
        obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        rfl
      · intro index marked
        exact PettaCompoundSelectedWork.primitive_choices control context origins head destination older [value]
          (active index marked) ⟨arguments, atCall⟩ (fun recipe => tail recipe (by simp [parseHead]))
  | primitive state values ordinary known returned =>
      apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending _ mark pendingMarks
        callerMark parentMarks held rfl front (.inr notCommit) _ _ _
      intro active
      apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (control, context, origins) (primitiveWork control context origins destination older values) mark
      · intro item member
        obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        rfl
      · intro index marked
        exact PettaCompoundSelectedWork.primitive_answers (allocator, ⟨world, current :: parents⟩) current parents control context
          origins pending head arguments destination older environment state values rfl front atCall resolved noQuery noCase
          returned (active index marked)
  | equations selected ordinary known notIO declared selectedRows =>
      have notQuery : head ≠ "match" := by
        intro same
        rw [same] at known
        cases known
      apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (allocator, ⟨world, current :: parents⟩) current parents (control, context, origins) pending _ mark pendingMarks
        callerMark parentMarks held rfl front (.inr notCommit) _ _ _
      intro active
      apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
        (control, context, origins) (selected.map fun choice => (predicateEntry pending.length choice.2, context, origins ++ [choice.1])) mark
      · intro item member
        obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
        rfl
      · intro index marked item member
        obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
        exact PettaCompoundSelectedWork.equation_choices
          (protectControl control (collectionSupport ⟨world, current :: parents⟩)) context origins head
          (arguments.map (read environment)) destination older _ selected pending.length
          (protected_control_marked control context origins _ active index marked) ⟨arguments, atCall⟩
          (fun recipe => tail recipe notQuery) selectedRows choice present
  | parseFault | parseAllocation | parseArity | primitiveFault | unserved => exact call_keeps _ _ _ held

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
