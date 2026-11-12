import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedFrameTransport
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnBoundary

/-!
# Compound returns instantiate the shared typed-phase transport

Actual row capture requires callable admission. The remaining argument and
inner-return phases are the same transport theorem used by variable returns.
Only the independently proved positional obligation differs. No additional
assumption is made about guard success, guard multiplicity or body completion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay

theorem transport_laws {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom) :
    PettaSelectedFrameTransport.Laws (Holds (User := User) program saved argument) where
  extendOrigins := fun held _ => held
  protect := fun held operations source => protect_keeps held operations source
  update := fun control context origins frame rest held calls after updated extended goals destination =>
    update_inner control context origins frame rest held calls after updated extended goals destination
  pop := fun control context origins frame rest held calls => pop_inner control context origins frame rest held calls

def Replaces {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom) (index : Nat)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (pending : List (Work User)) (reply : Step User) : Prop :=
  PettaSelectedFrameTransport.Replaces (Holds program saved argument) index source current parents pending reply

theorem enter_rows {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom} {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Holds program saved argument index (control, context, origins))
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false)
    (called : callable program head = true) :
    Replaces program saved argument (index + 1) source current parents pending
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
        older row occurrence atCall ordinary called) operations source
    · exact .inl ⟨_, rfl⟩

theorem next_argument {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom} {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (rest : List CallFrame)
    (held : Holds program saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    Replaces program saved argument (index + 1) source current parents pending
      (nextArgument operations source current parents control context origins pending frame rest) :=
  PettaSelectedFrameTransport.next_argument (transport_laws program saved argument) operations source current parents control
    context origins pending frame rest held calls

theorem argument_continuations {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (operations : Services User) (source : State User) (control : DControl)
    (context : Context User) (origins : List Nat) (frame : CallFrame) (rest : List CallFrame) (slot : Atom) (stores : List Store)
    (held : Holds program saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    ∀ item ∈ argumentContinuations operations source control context origins frame rest slot stores,
      Holds program saved argument (index + 1) item :=
  PettaSelectedFrameTransport.argument_continuations (transport_laws program saved argument) operations source control context
    origins frame rest slot stores held calls

theorem argument_guard {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom} {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (rest : List CallFrame) (formal : Ty String) (slot value : Atom)
    (held : Holds program saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    Replaces program saved argument (index + 1) source current parents pending
      (consumeArgument operations source current parents control context origins pending frame rest formal slot value) :=
  PettaSelectedFrameTransport.argument_guard (transport_laws program saved argument) operations source current parents control
    context origins pending frame rest formal slot value held calls

theorem body_guard {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom} {index : Nat}
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (rest : List CallFrame) (value : Atom)
    (held : Holds program saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    Replaces program saved argument index source current parents pending
      (consumeBody operations source current parents control context origins pending frame rest value) :=
  PettaSelectedFrameTransport.body_guard (transport_laws program saved argument) operations source current parents control context
    origins pending frame rest value held calls

/-- A reached mark at position zero supplies the actual typed boundary;
the existing solver, guard and caller restoration remain unchanged. -/
theorem terminal_dispatch {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User)) (outside : List CallFrame)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = saved :: outside) (depth : saved.scopeDepth = source.2.scopes.length)
    (phase : saved.phase = .body) (terminal : control.goals = []) (name : String)
    (slot : control.destination = .var name) (held : Holds program saved argument 0 (control, context, origins)) :
    PettaOccurrenceOverlay.step operations .eagerValue program source =
      match resolve control.bindings with
      | none => .call (.source (.branch .invalidEnvironment)) source
      | some environment => consumeBody operations source current parents control context origins pending saved outside
          (read environment argument) :=
  PettaCompoundReturnBoundary.dispatch program saved argument operations source current parents control context origins
    pending outside scopes frontier calls depth phase terminal name slot (head_alias held)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork
