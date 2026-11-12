import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkContracts

/-!
# Actual collection scope changes carry the selected caller mark

Child work is unrestricted. The source's saved caller carries the outer
return obligation and restores it after the actual copied answer list. Both
scope changes use the deterministic metadata update.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks Stack)

theorem collapse_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (expression destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (goals : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older)
    (child : Scope User)
    (atCaller : child.caller = some ({control with goals := older}, destination, context, origins))
    (allocator : Allocator) (world : EagerDFS.World) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (allocator, ⟨world, child :: {current with frontier := pending} :: parents⟩)) :=
  PettaMarkedTransitions.collapse_keeps source current parents control context origins pending mark pendingMarks callerMark
    parentMarks held scopes front older destination
    (fun _ returning => PettaSelectedReturnWork.collapse_caller control context origins returning expression destination older goals)
    child atCaller allocator world

theorem collection_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (child parent : Scope User) (parents : List (Scope User))
    (childMarks parentMarks : Marks) (outsideMarks : List Marks)
    (held : Stack saved argument (childMarks :: parentMarks :: outsideMarks) source.2.scopes)
    (scopes : source.2.scopes = child :: parent :: parents)
    (caller : CollectionCaller (Context User)) (atCaller : child.caller = some caller)
    (copies : List (Atom × List Atom)) (allocator : Allocator) (world : EagerDFS.World) :
    Preserves saved argument (childMarks :: parentMarks :: outsideMarks) source
      (.silent (allocator, ⟨world, {parent with frontier := Source.resumeCopies copies caller :: parent.frontier} :: parents⟩)) :=
  PettaMarkedTransitions.collection_keeps source child parent parents childMarks parentMarks outsideMarks held scopes caller
    atCaller copies (fun _ returning => PettaSelectedReturnWork.collection_copies copies caller returning) allocator world

theorem commit_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending younger kept : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (older : List EagerDFS.Destination.Goal)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (goals : control.goals = .commit :: older) (partition : pending = younger ++ kept)
    (sourceLane : frameActive source = false) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (source.1, ⟨source.2.world,
        {current with frontier := ({control with goals := older}, context, origins) :: kept} :: parents⟩)) :=
  PettaMarkedTransitions.commit_keeps source current parents control context origins pending younger kept mark pendingMarks
    callerMark parentMarks older held scopes front goals partition sourceLane
    (fun _ returning => PettaSelectedReturnWork.committing control context origins returning older goals)

theorem source_collection_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    {source after : State User} {marks : List Marks}
    (step : Source.CollectionReturn Source.FreshOperations.owned source after)
    (held : Stack saved argument marks source.2.scopes) :
    Preserves saved argument marks source (.silent after) :=
  PettaMarkedTransitions.source_collection_keeps step held
    (fun copies caller _ returning => PettaSelectedReturnWork.collection_copies copies caller returning)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
