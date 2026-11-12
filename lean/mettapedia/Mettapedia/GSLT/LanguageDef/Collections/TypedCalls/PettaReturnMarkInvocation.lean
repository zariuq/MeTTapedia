import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkSurface

/-!
# Real primitive and equation invocations keep deterministic marks

The source dispatcher supplies complete selected frontiers. Parsed values,
primitive answers, empty replies and duplicate equation occurrences keep
their real positions and world. No callee result specification is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks Stack WorkMarked)

theorem protected_control_marked {User : Type} {saved : CallFrame} {argument : Atom} {mark : Option Nat}
    (control : DControl) (context : Context User) (origins : List Nat) (boundary : Finset String)
    (held : WorkMarked saved argument mark (control, context, origins)) :
    WorkMarked saved argument mark (protectControl control boundary, context, origins) := by
  intro index marked
  obtain ⟨above, outside, length, calls, returning⟩ := held index marked
  exact ⟨above, outside, length, calls, returning.protect_control boundary⟩

theorem invocation_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    {program : SpaceSemantics.Program} {allocator : Allocator} {world : EagerDFS.World}
    {current : Scope User} {parents : List (Scope User)} {control : DControl} {context : Context User}
    {origins : List Nat} {pending : List (Work User)} {head : String} {arguments : List Atom}
    {destination : Atom} {older : List EagerDFS.Destination.Goal} {environment : Environment}
    {action : Source.ScopeAction Allocator (Context User)}
    (step : Source.Invocation Source.FreshOperations.owned program allocator world current parents control context origins pending
      head arguments destination older environment action)
    (front : current.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (noQuery : Bridges.ScopedQuerySource.queryStep (allocator, ⟨world, current :: parents⟩) = none)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern
      (allocator, ⟨world, current :: parents⟩) = none)
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) (current :: parents)) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks)
      (allocator, ⟨world, current :: parents⟩) (liftSource action) := by
  have tail (name : String) : Bridges.ScopedReturnObligation.Pending (.var name) control.destination control.goals →
      Bridges.ScopedReturnObligation.Pending (.var name) control.destination older := by
    intro returning
    exact Bridges.ScopedReturnRawEntry.pending_raw_invocation_tail name control.destination
      (allocator, ⟨world, current :: parents⟩) current parents control context origins pending head arguments destination older
      environment rfl front atCall resolved returning noQuery noCase
  cases step with
  | parsed text value after parseHead input returned =>
      apply installed_scope_keeps _ current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks
        held rfl front (.inr (invoke_not_commit atCall)) _ _ _
      intro active
      apply same_count_generated (control, context, origins) _ mark
      · intro item member
        obtain ⟨entry, _present, rfl⟩ := List.mem_map.mp member
        rfl
      · intro index marked
        exact PettaSelectedReturnWork.primitive_choices control context origins destination older [value] (active index marked) tail
  | primitive state values ordinary known returned =>
      apply installed_scope_keeps _ current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks
        held rfl front (.inr (invoke_not_commit atCall)) _ _ _
      intro active
      apply same_count_generated (control, context, origins) _ mark
      · intro item member
        obtain ⟨entry, _present, rfl⟩ := List.mem_map.mp member
        rfl
      · intro index marked
        exact PettaSelectedReturnWork.primitive_choices control context origins destination older values (active index marked) tail
  | equations selected ordinary known notIO declared selectedRows =>
      apply installed_scope_keeps _ current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks
        held rfl front (.inr (invoke_not_commit atCall)) _ _ _
      intro active
      apply same_count_generated (control, context, origins) _ mark
      · intro item member
        obtain ⟨choice, _present, rfl⟩ := List.mem_map.mp member
        rfl
      · intro index marked item member
        obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
        exact PettaSelectedReturnWork.equation_choices program (protectControl control (collectionSupport ⟨world, current :: parents⟩))
          context origins head (arguments.map (read environment)) destination older _ selected pending.length
          (protected_control_marked control context origins _ active index marked) tail selectedRows choice present
  | parseFault | parseAllocation | parseArity | primitiveFault | unserved => exact call_keeps _ _ _ held

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
