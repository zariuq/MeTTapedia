import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedOperations
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTyped

/-!
# Compound obligations instantiate the computed typed-update proof

The frame laws are earned independently by the compound invariant. Row
capture additionally requires the actual callable-head admission. All
guard replies, duplicates and missing-service requests use the existing
operation and its actual generated continuations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

theorem rows_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false) (called : callable program head = true) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (enterRows operations source current parents control context origins pending head arguments destination older) :=
  PettaMarkedTyped.rows_keeps (PettaCompoundSelectedWork.transport_laws program saved argument) operations source current
    parents control context origins pending mark pendingMarks callerMark parentMarks head arguments destination older held
    scopes front atCall (fun _index tracked row occurrence => PettaCompoundSelectedWork.row_work control context origins tracked
      source.2.scopes.length head arguments destination older row occurrence atCall ordinary called)

theorem next_argument_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (frame : CallFrame) (outside : List CallFrame)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length)
    (phase : frame.phase = .nextArgument) (notSelected : mark ≠ some 0) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (nextArgument operations source current parents control context origins pending frame outside) :=
  PettaMarkedTyped.next_argument_keeps (PettaCompoundSelectedWork.transport_laws program saved argument) operations source
    current parents control context origins pending mark pendingMarks callerMark parentMarks frame outside held scopes front
    calls depth phase notSelected

theorem argument_guard_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length)
    (terminal : control.goals = []) (notSelected : mark ≠ some 0) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (consumeArgument operations source current parents control context origins pending frame outside formal slot value) :=
  PettaMarkedTyped.argument_guard_keeps (PettaCompoundSelectedWork.transport_laws program saved argument) operations source
    current parents control context origins pending mark pendingMarks callerMark parentMarks frame outside formal slot value
    held scopes front calls depth terminal notSelected

theorem body_guard_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length) (terminal : control.goals = []) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (consumeBody operations source current parents control context origins pending frame outside value) :=
  PettaMarkedTyped.body_guard_keeps (PettaCompoundSelectedWork.transport_laws program saved argument) operations source current
    parents control context origins pending mark pendingMarks callerMark parentMarks frame outside value held scopes front calls depth terminal

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
