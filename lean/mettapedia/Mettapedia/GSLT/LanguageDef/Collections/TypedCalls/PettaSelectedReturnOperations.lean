import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedFrameTransport

/-!
# Actual typed phases preserve a selected frame below their owned prefix

Row entry pushes one owned frame. Argument phases update only that frame;
its return pops it. The selected body frame and inherited suffix stay in
place. Missing service retains the source state, and served empty/repeated
continuation lists keep their actual meanings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames

theorem active_prefix {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    {control : DControl} {context : Context User} {origins : List Nat} {frame : CallFrame} {rest : List CallFrame}
    (held : Holds saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    ∃ above outside, above.length = index ∧ rest = above ++ saved :: outside ∧
      Frames argument control (frame :: above) := by
  obtain ⟨owned, outside, length, stack, returning⟩ := held
  change context.calls = owned ++ saved :: outside at stack
  cases owned with
  | nil => simp only [List.length_nil] at length; omega
  | cons inner above =>
      have same : frame :: rest = inner :: (above ++ saved :: outside) := calls.symm.trans stack
      obtain ⟨heads, tails⟩ := List.cons.inj same
      subst inner
      exact ⟨above, outside, by simp only [List.length_cons] at length; omega, tails, returning⟩

theorem update_inner {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat) (frame : CallFrame) (rest : List CallFrame)
    (held : Holds saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) (after : DControl) (updated : CallFrame)
    (extended : RefinementTransport.Extends control.bindings after.bindings)
    (goals : updated.callerGoals = frame.callerGoals)
    (destination : updated.callerDestination = frame.callerDestination) :
    Holds saved argument (index + 1) (after, {context with calls := updated :: rest}, origins) := by
  obtain ⟨above, outside, length, stack, returning⟩ := active_prefix held calls
  refine ⟨updated :: above, outside, ?_, ?_, returning.update_top extended goals destination⟩
  · simp only [List.length_cons, length]
  · simp only [List.cons_append, stack]

theorem pop_inner {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat) (frame : CallFrame) (rest : List CallFrame)
    (held : Holds saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    Holds saved argument index (resumeCaller control frame, {context with calls := rest}, origins) := by
  obtain ⟨above, outside, length, stack, returning⟩ := active_prefix held calls
  exact ⟨above, outside, length, stack, returning.resume_top⟩

def Replaces {User : Type} (saved : CallFrame) (argument : Atom) (index : Nat)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (pending : List (Work User)) (reply : Step User) : Prop :=
  PettaSelectedFrameTransport.Replaces (Holds saved argument) index source current parents pending reply

theorem transport_laws {User : Type} (saved : CallFrame) (argument : Atom) :
    PettaSelectedFrameTransport.Laws (Holds (User := User) saved argument) where
  extendOrigins := fun held _ => held
  protect := fun held operations source => protect_keeps held operations source
  update := fun control context origins frame rest held calls after updated extended goals destination =>
    update_inner control context origins frame rest held calls after updated extended goals destination
  pop := fun control context origins frame rest held calls => pop_inner control context origins frame rest held calls

theorem enter_rows {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Holds saved argument index (control, context, origins))
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false) :
    Replaces saved argument (index + 1) source current parents pending
      (enterRows operations source current parents control context origins pending head arguments destination older) := by
  unfold enterRows
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · dsimp only
    split
    · refine .inr ⟨_, rfl, ?_⟩
      intro item member
      obtain ⟨⟨row, occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
      exact protect_keeps (row_work control context origins held source.2.scopes.length head arguments destination
        older row occurrence atCall ordinary) operations source
    · exact .inl ⟨_, rfl⟩

theorem next_argument {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (rest : List CallFrame)
    (held : Holds saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    Replaces saved argument (index + 1) source current parents pending
      (nextArgument operations source current parents control context origins pending frame rest) :=
  PettaSelectedFrameTransport.next_argument (transport_laws saved argument) operations source current parents control context
    origins pending frame rest held calls

theorem argument_continuations {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (operations : Services User) (source : State User) (control : DControl) (context : Context User)
    (origins : List Nat) (frame : CallFrame) (rest : List CallFrame) (slot : Atom) (stores : List Store)
    (held : Holds saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    ∀ item ∈ argumentContinuations operations source control context origins frame rest slot stores,
      Holds saved argument (index + 1) item :=
  PettaSelectedFrameTransport.argument_continuations (transport_laws saved argument) operations source control context origins
    frame rest slot stores held calls

theorem argument_guard {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (rest : List CallFrame) (formal : Ty String) (slot value : Atom)
    (held : Holds saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    Replaces saved argument (index + 1) source current parents pending
      (consumeArgument operations source current parents control context origins pending frame rest formal slot value) :=
  PettaSelectedFrameTransport.argument_guard (transport_laws saved argument) operations source current parents control context
    origins pending frame rest formal slot value held calls

theorem body_guard {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (rest : List CallFrame) (value : Atom)
    (held : Holds saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    Replaces saved argument index source current parents pending
      (consumeBody operations source current parents control context origins pending frame rest value) :=
  PettaSelectedFrameTransport.body_guard (transport_laws saved argument) operations source current parents control context
    origins pending frame rest value held calls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork
