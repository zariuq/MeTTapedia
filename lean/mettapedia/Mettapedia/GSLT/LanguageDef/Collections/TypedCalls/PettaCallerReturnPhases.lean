import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnFrames

/-!
# Actual typed-call continuation operations preserve the saved return

The returned type stores may be absent, empty, singleton or repeated. The
proof concerns each real produced work occurrence and keeps the reached
term record. It does not presume a guard succeeds or choose a guard answer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnPhases

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open PettaOccurrenceOverlay PettaCallerReturnFrames

def WorkHolds {User : Type} (inputs : User → Atom) (work : Work User) : Prop :=
  Frames (inputs work.2.1.user) work.1 work.2.1.calls

theorem row_work_holds {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (control : DControl) (context : Context User) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (row : Row) (occurrence : Nat)
    (held : Frames (inputs context.user) control context.calls)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false) :
    let work := rowWork control context origins source.2.scopes.length head arguments destination older row occurrence
    WorkHolds inputs (protect services source work.1 work.2.1, work.2) := by
  exact (row_work_captures_return (inputs context.user) control context origins source.2.scopes.length
    head arguments destination older row occurrence held atCall ordinary).protect services source _

theorem argument_continuations_hold {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (slot : Atom) (stores : List Store)
    (held : Frames (inputs context.user) control (frame :: outside)) :
    ∀ work ∈ argumentContinuations services source control context origins frame outside slot stores,
      WorkHolds inputs work := by
  intro work present
  obtain ⟨⟨store, occurrence⟩, _present, rfl⟩ := List.mem_map.mp present
  apply Frames.protect
  exact held.update_top (.refl _) rfl rfl

theorem body_continuations_hold {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (stores : List Store)
    (held : Frames (inputs context.user) control (frame :: outside)) :
    ∀ work ∈ (stores.zipIdx.map fun (_, occurrence) =>
      (protect services source (resumeCaller control frame) {context with calls := outside},
        {context with calls := outside}, origins ++ [occurrence])), WorkHolds inputs work := by
  intro work present
  obtain ⟨⟨store, occurrence⟩, _present, rfl⟩ := List.mem_map.mp present
  exact held.resume_top.protect services source _

theorem ready_body_holds {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (control : DControl) (context : Context User)
    (frame : CallFrame) (outside : List CallFrame)
    (held : Frames (inputs context.user) control (frame :: outside)) :
    Frames (inputs context.user)
      (protect services source
        {control with goals := [.invoke frame.head frame.ready frame.callDestination], destination := frame.callDestination}
        {context with calls := {frame with phase := .body} :: outside})
      ({frame with phase := .body} :: outside) := by
  apply Frames.protect
  exact held.update_top (after := {control with goals := [.invoke frame.head frame.ready frame.callDestination], destination := frame.callDestination}) (.refl _) rfl rfl

theorem raw_argument_holds {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (control : DControl) (context : Context User)
    (frame : CallFrame) (outside : List CallFrame) (argument : Atom) (remaining : List (Ty String × Atom))
    (held : Frames (inputs context.user) control (frame :: outside)) :
    let advanced := {frame with remaining, ready := frame.ready ++ [argument], index := frame.index + 1}
    Frames (inputs context.user) (protect services source control {context with calls := advanced :: outside})
      (advanced :: outside) := by
  dsimp only
  apply Frames.protect
  exact held.update_top (.refl _) rfl rfl

theorem evaluated_argument_holds {User : Type} (inputs : User → Atom) (services : Services User)
    (source : State User) (control : DControl) (context : Context User)
    (frame : CallFrame) (outside : List CallFrame) (argument slot : Atom) (formal : Ty String)
    (remaining : List (Ty String × Atom))
    (held : Frames (inputs context.user) control (frame :: outside)) :
    let prepared := protect services source control context
    let advanced := {frame with remaining, phase := .argument formal slot}
    Frames (inputs context.user)
      (protect services source {prepared with goals := [.evaluate argument slot], destination := slot}
        {context with calls := advanced :: outside}) (advanced :: outside) := by
  dsimp only
  apply Frames.protect
  exact held.update_top
    (after := {protect services source control context with goals := [.evaluate argument slot], destination := slot})
    (.refl _) rfl rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnPhases
