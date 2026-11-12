import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaContextFacts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopes
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork

/-!
# Inner call frames cannot belong to a shallower scope than their callers

The order is about actual frame occurrences, independent of their values,
return recipes or logical bindings. Together with the existing upper scope
bounds it identifies the active depth of a selected return's owned prefix.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrder

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay

def Ordered {User : Type} (context : Context User) : Prop :=
  context.calls.Pairwise (fun inner outer => outer.scopeDepth ≤ inner.scopeDepth)

def Safe {User : Type} (source : State User) : Prop := PettaContextFacts.Safe (@Ordered User) source
def Keeps {User : Type} (reply : Step User) : Prop := PettaContextFacts.Keeps (@Ordered User) reply

theorem empty {User : Type} (user : User) : Ordered (⟨user, []⟩ : Context User) := .nil

theorem push {User : Type} {context : Context User} (ordered : Ordered context) (frame : CallFrame)
    (bounds : ∀ outer ∈ context.calls, outer.scopeDepth ≤ frame.scopeDepth) :
    Ordered {context with calls := frame :: context.calls} := by
  exact List.pairwise_cons.mpr ⟨bounds, ordered⟩

theorem update {User : Type} {context : Context User} {frame : CallFrame} {outside : List CallFrame}
    (ordered : Ordered context) (calls : context.calls = frame :: outside) (updated : CallFrame)
    (depth : updated.scopeDepth = frame.scopeDepth) : Ordered {context with calls := updated :: outside} := by
  have actual : (frame :: outside).Pairwise (fun inner outer => outer.scopeDepth ≤ inner.scopeDepth) := by
    simpa only [Ordered, calls] using ordered
  have prior := List.pairwise_cons.mp actual
  apply List.pairwise_cons.mpr
  exact ⟨fun outer present => by simpa only [depth] using prior.1 outer present, prior.2⟩

theorem pop {User : Type} {context : Context User} {frame : CallFrame} {outside : List CallFrame}
    (ordered : Ordered context) (calls : context.calls = frame :: outside) : Ordered {context with calls := outside} := by
  have actual : (frame :: outside).Pairwise (fun inner outer => outer.scopeDepth ≤ inner.scopeDepth) := by
    simpa only [Ordered, calls] using ordered
  exact (List.pairwise_cons.mp actual).2

theorem member_depth {User : Type} {saved : CallFrame} {depth : Nat}
    {context : Context User} {frame : CallFrame} {outside : List CallFrame}
    (ordered : Ordered context) (bounded : PettaFrameScopes.CallsAt depth context)
    (member : saved ∈ context.calls)
    (owner : saved.scopeDepth = depth) (calls : context.calls = frame :: outside) : frame.scopeDepth = depth := by
  have bounds := bounded frame (calls ▸ List.mem_cons_self)
  have lower : saved.scopeDepth ≤ frame.scopeDepth := by
    rw [calls] at member
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_refl _
    · have actual : (frame :: outside).Pairwise (fun inner outer => outer.scopeDepth ≤ inner.scopeDepth) := by
        simpa only [Ordered, calls] using ordered
      exact (List.pairwise_cons.mp actual).1 saved later
  omega

theorem selected_depth {User : Type} {saved : CallFrame} {argument : Atom} {index depth : Nat}
    {control : DControl} {context : Context User} {origins : List Nat} {frame : CallFrame} {outside : List CallFrame}
    (ordered : Ordered context) (bounded : PettaFrameScopes.CallsAt depth context)
    (selected : PettaSelectedReturnWork.Holds saved argument index (control, context, origins))
    (owner : saved.scopeDepth = depth) (calls : context.calls = frame :: outside) : frame.scopeDepth = depth :=
  member_depth ordered bounded (List.mem_of_getElem? (PettaSelectedReturnWork.selected_position selected)) owner calls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrder
