import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnBoundary

/-!
# Marked host scopes earn the selected result-boundary view

The active frontier label must explicitly be position zero. An absent mark,
a saved caller without a corresponding scope caller, or a different frame
position cannot supply this boundary evidence. Solver failure still remains
a request in the actual dispatch theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay

theorem active_mark {User : Type} {saved : CallFrame} {argument : Atom}
    (current : Scope User) (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (index : Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat)
    (held : ScopeHolds saved argument ⟨some index :: pendingMarks, callerMark⟩ current)
    (frontier : current.frontier = (control, context, origins) :: pending) :
    PettaSelectedReturnWork.Holds saved argument index (control, context, origins) :=
  PettaScopeMarks.active_work current control context origins pending index pendingMarks callerMark held frontier

theorem marked_boundary_view {User : Type} (saved : CallFrame) (argument : Atom) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack saved argument (⟨some 0 :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (depth : saved.scopeDepth = source.2.scopes.length) (phase : saved.phase = .body)
    (terminal : control.goals = []) : Nonempty (PettaSelectedReturnBoundary.View saved argument source) := by
  have owner := (List.forall₂_cons.mp (scopes ▸ held)).1
  exact PettaSelectedReturnBoundary.view_of_mark saved argument source current parents control context origins pending
    scopes frontier (active_mark current control context origins pending 0 pendingMarks callerMark owner frontier)
    depth phase terminal

theorem marked_dispatch {User : Type} (saved : CallFrame) (argument : Atom)
    (operations : Services User) (program : SpaceSemantics.Program) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack saved argument (⟨some 0 :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (depth : saved.scopeDepth = source.2.scopes.length) (phase : saved.phase = .body)
    (terminal : control.goals = []) :
    ∃ outside, context.calls = saved :: outside ∧
      PettaOccurrenceOverlay.step operations .eagerValue program source =
        match resolve control.bindings with
        | none => .call (.source (.branch .invalidEnvironment)) source
        | some environment => consumeBody operations source current parents control context origins pending saved outside
            (read environment argument) := by
  have owner := (List.forall₂_cons.mp (scopes ▸ held)).1
  have selected := active_mark current control context origins pending 0 pendingMarks callerMark owner frontier
  obtain ⟨above, outside, length, calls, returning⟩ := selected
  have empty : above = [] := List.eq_nil_of_length_eq_zero length
  subst above
  have selected : PettaSelectedReturnWork.Holds saved argument 0 (control, context, origins) :=
    ⟨[], outside, rfl, calls, returning⟩
  let view : PettaSelectedReturnBoundary.View saved argument source :=
    ⟨current, parents, control, context, origins, pending, outside, scopes, frontier, calls, depth, phase, terminal, selected⟩
  exact ⟨outside, calls, PettaSelectedReturnBoundary.dispatch operations program source view⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes
