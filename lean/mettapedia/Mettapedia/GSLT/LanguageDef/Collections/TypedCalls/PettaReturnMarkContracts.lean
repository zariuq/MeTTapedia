import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTransitions

/-!
# Contracts for the deterministic annotation update

Preservation uses the marks returned by `advance`, not an existential choice
of an untracked layout. Local installation exposes the obligation each real
generated occurrence must satisfy. The semantic operation laws discharge
that obligation; this module alone is not dispatcher coverage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks WorkMarked Frontier ScopeHolds Stack)

theorem advance_identity {User : Type} {saved : CallFrame} {argument : Atom}
    (marks : List Marks) (source : State User) (held : Stack saved argument marks source.2.scopes) :
    advance marks source source = some marks := advance_stack_identity marks source held

def Preserves {User : Type} (saved : CallFrame) (argument : Atom) (marks : List Marks)
    (source : State User) (reply : Step User) : Prop :=
  PettaMarkedTransitions.Preserves (PettaSelectedReturnWork.Holds saved argument) marks source reply

theorem call_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (marks : List Marks) (source : State User) (request : Request)
    (held : Stack saved argument marks source.2.scopes) :
    Preserves saved argument marks source (.call request source) := PettaMarkedTransitions.call_keeps marks source request held

theorem annotated_frontier {User : Type} (saved : CallFrame) (argument : Atom) (mark : Option Nat)
    (before : Work User) (generated : List (Work User))
    (held : ∀ item ∈ generated,
      WorkMarked saved argument (shift before.2.1.calls.length item.2.1.calls.length mark) item) :
    Frontier saved argument
      (generated.map (fun item => shift before.2.1.calls.length item.2.1.calls.length mark)) generated :=
  PettaMarkedTransitions.annotated_frontier (PettaSelectedReturnWork.Holds saved argument) mark before generated held

theorem install_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User)) (before : Work User)
    (pending generated : List (Work User)) (mark : Option Nat) (pendingMarks : List (Option Nat))
    (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = before :: pending)
    (ordinary : frameActive source = true ∨ ∀ older, before.1.goals ≠ .commit :: older)
    (produced : WorkMarked saved argument mark before →
      ∀ item ∈ generated, WorkMarked saved argument (shift before.2.1.calls.length item.2.1.calls.length mark) item) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (install source current parents generated pending)) :=
  PettaMarkedTransitions.install_keeps source current parents before pending generated mark pendingMarks callerMark parentMarks
    held scopes front ordinary produced

theorem same_count_generated {User : Type} {saved : CallFrame} {argument : Atom}
    (before : Work User) (generated : List (Work User)) (mark : Option Nat)
    (counts : ∀ item ∈ generated, item.2.1.calls.length = before.2.1.calls.length)
    (held : ∀ index, mark = some index → ∀ item ∈ generated, PettaSelectedReturnWork.Holds saved argument index item) :
    ∀ item ∈ generated, WorkMarked saved argument (shift before.2.1.calls.length item.2.1.calls.length mark) item :=
  PettaMarkedTransitions.same_count_generated before generated mark counts held

theorem installed_data_irrelevant {User : Type} (marks : List Marks) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (generated pending : List (Work User))
    (allocator : Allocator) (world : EagerDFS.World) (collected : List CollectedAnswer) :
    advance marks source
      (allocator, ⟨world, {current with frontier := generated ++ pending, collected} :: parents⟩) =
      advance marks source (install source current parents generated pending) :=
  PettaMarkedTransitions.installed_data_irrelevant marks source current parents generated pending allocator world collected

theorem installed_scope_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User)) (before : Work User)
    (pending generated : List (Work User)) (mark : Option Nat) (pendingMarks : List (Option Nat))
    (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = before :: pending)
    (ordinary : frameActive source = true ∨ ∀ older, before.1.goals ≠ .commit :: older)
    (produced : WorkMarked saved argument mark before →
      ∀ item ∈ generated, WorkMarked saved argument (shift before.2.1.calls.length item.2.1.calls.length mark) item)
    (allocator : Allocator) (world : EagerDFS.World) (collected : List CollectedAnswer) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (allocator, ⟨world, {current with frontier := generated ++ pending, collected} :: parents⟩)) :=
  PettaMarkedTransitions.installed_scope_keeps source current parents before pending generated mark pendingMarks callerMark
    parentMarks held scopes front ordinary produced allocator world collected

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
