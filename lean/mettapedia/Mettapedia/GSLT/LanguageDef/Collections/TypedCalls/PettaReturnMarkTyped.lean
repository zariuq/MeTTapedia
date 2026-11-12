import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkContracts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnOperations
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTyped

/-!
# Typed operations discharge the deterministic mark-update contracts

The generated marks come from actual frame counts. Row entry pushes the
selected position; argument progress does not. An owned callee return pops
the position, while the selected return retires it. Actual guard semantics
remain those of the existing operation and its result-boundary theorems.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks WorkMarked Stack)

theorem protect_marked {User : Type} {saved : CallFrame} {argument : Atom} {mark : Option Nat} {item : Work User}
    (held : WorkMarked saved argument mark item) (operations : Services User) (source : State User) :
    WorkMarked saved argument mark (protect operations source item.1 item.2.1, item.2) :=
  PettaMarkedTyped.protect_marked (PettaSelectedReturnWork.transport_laws saved argument) held operations source

theorem updated_frame_marked {User : Type} {saved : CallFrame} {argument : Atom} {mark : Option Nat}
    (control : DControl) (context : Context User) (origins : List Nat) (frame : CallFrame) (outside : List CallFrame)
    (held : WorkMarked saved argument mark (control, context, origins)) (notSelected : mark ≠ some 0)
    (calls : context.calls = frame :: outside) (after : DControl) (updated : CallFrame)
    (extended : RefinementTransport.Extends control.bindings after.bindings)
    (goals : updated.callerGoals = frame.callerGoals)
    (destination : updated.callerDestination = frame.callerDestination) :
    WorkMarked saved argument mark (after, {context with calls := updated :: outside}, origins) :=
  PettaMarkedTyped.updated_frame_marked (PettaSelectedReturnWork.transport_laws saved argument) control context origins frame
    outside held notSelected calls after updated extended goals destination

theorem rows_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (enterRows operations source current parents control context origins pending head arguments destination older) :=
  PettaMarkedTyped.rows_keeps (PettaSelectedReturnWork.transport_laws saved argument) operations source current parents control
    context origins pending mark pendingMarks callerMark parentMarks head arguments destination older held scopes front atCall
    (fun _index tracked row occurrence => PettaSelectedReturnWork.row_work control context origins tracked source.2.scopes.length
      head arguments destination older row occurrence atCall ordinary)

theorem next_argument_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (frame : CallFrame) (outside : List CallFrame)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length)
    (phase : frame.phase = .nextArgument) (notSelected : mark ≠ some 0) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (nextArgument operations source current parents control context origins pending frame outside) :=
  PettaMarkedTyped.next_argument_keeps (PettaSelectedReturnWork.transport_laws saved argument) operations source current parents
    control context origins pending mark pendingMarks callerMark parentMarks frame outside held scopes front calls depth phase notSelected

theorem argument_guard_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length)
    (terminal : control.goals = []) (notSelected : mark ≠ some 0) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (consumeArgument operations source current parents control context origins pending frame outside formal slot value) :=
  PettaMarkedTyped.argument_guard_keeps (PettaSelectedReturnWork.transport_laws saved argument) operations source current parents
    control context origins pending mark pendingMarks callerMark parentMarks frame outside formal slot value held scopes front calls depth
    terminal notSelected

theorem body_guard_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length)
    (terminal : control.goals = []) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (consumeBody operations source current parents control context origins pending frame outside value) :=
  PettaMarkedTyped.body_guard_keeps (PettaSelectedReturnWork.transport_laws saved argument) operations source current parents
    control context origins pending mark pendingMarks callerMark parentMarks frame outside value held scopes front calls depth terminal

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
