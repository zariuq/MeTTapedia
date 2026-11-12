import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedBoundary

/-!
# A retained region machine with same-step canonical handoff

The controller owns a split local context until an inherited frame becomes
active. At that boundary it executes the host's actual next transition and
keeps subsequent work in host mode. There is no synthetic silent handoff tick.

Erasing the mode and flattening local contexts gives the exact host run for
every finite budget, including ordered packets and retained requests. This is
an operational model theorem, not an instruction-count or native-code theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedMachine

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaInheritedContext (LocalState HostResult)

abbrev Mode (User : Type) := LocalState User ⊕ State User
abbrev Action (User : Type) := Transition (Mode User) CollectedAnswer (State User) Request

def decode {User : Type} : Mode User → State User
  | .inl source => PettaInheritedContext.state source
  | .inr source => source

def localAction {User : Type} : Step (Context User) → Action User
  | .silent next => .silent (.inl next)
  | .publish events next => .publish events (.inl next)
  | .finish final => .finish (PettaInheritedContext.state final)
  | .call request retained => .call request (.inl retained)
  | .fail events => .fail events

def hostAction {User : Type} : Step User → Action User
  | .silent next => .silent (.inr next)
  | .publish events next => .publish events (.inr next)
  | .finish final => .finish final
  | .call request retained => .call request (.inr retained)
  | .fail events => .fail events

def eraseAction {User : Type} : Action User → Step User
  | .silent next => .silent (decode next)
  | .publish events next => .publish events (decode next)
  | .finish final => .finish final
  | .call request retained => .call request (decode retained)
  | .fail events => .fail events

def outcome {User : Type} : Outcome (Mode User) (State User) Request →
    Outcome (State User) (State User) Request
  | .finished final => .finished final
  | .suspended request retained => .suspended request (decode retained)
  | .stuck retained => .stuck (decode retained)
  | .exhausted retained => .exhausted (decode retained)
  | .faulted => .faulted

def step {User : Type} (original : Services User) (program : SpaceSemantics.Program) : Mode User → Action User
  | .inl source =>
      if PettaInheritedContext.boundary source then
        hostAction (PettaOccurrenceOverlay.step original .eagerValue program (PettaInheritedContext.state source))
      else localAction (PettaOccurrenceOverlay.step (PettaInheritedContext.services original) .eagerValue program source)
  | .inr source => hostAction (PettaOccurrenceOverlay.step original .eagerValue program source)

def machine {User : Type} (original : Services User) (program : SpaceSemantics.Program) :
    Machine (Mode User) CollectedAnswer (State User) Request where
  step source := some (step original program source)

theorem erase_host_action {User : Type} (reply : Step User) : eraseAction (hostAction reply) = reply := by
  cases reply <;> rfl

theorem erase_local_action {User : Type} (reply : Step (Context User)) :
    eraseAction (localAction reply) = PettaInheritedContext.action reply := by cases reply <;> rfl

theorem step_refines {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (source : Mode User) :
    eraseAction (step original program source) =
      PettaOccurrenceOverlay.step original .eagerValue program (decode source) := by
  cases source with
  | inr source => exact erase_host_action _
  | inl source =>
      cases checked : PettaInheritedContext.boundary source with
      | true => simp only [step, checked, if_true, erase_host_action, decode]
      | false =>
          simp only [step, checked, Bool.false_eq_true, if_false, erase_local_action, decode]
          exact (PettaInheritedContext.interior_step original program source checked).symm

theorem run_refines {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : Mode User) :
    let result := (machine original program).run fuel source
    (result.1, outcome result.2) =
      (PettaOccurrenceOverlay.machine original .eagerValue program).run fuel (decode source) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      simp only [Machine.run, machine, PettaOccurrenceOverlay.machine, ← step_refines original program source]
      cases advanced : step original program source with
      | silent next =>
          simpa only [advanced, eraseAction, machine, PettaOccurrenceOverlay.machine] using ih next
      | publish events next =>
          simpa only [advanced, eraseAction, machine, PettaOccurrenceOverlay.machine] using congrArg
            (fun result : HostResult User => (events ++ result.1, result.2)) (ih next)
      | finish final | call request retained | fail events => rfl

theorem run_in_host {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : State User) :
    let result := (machine original program).run fuel (.inl (PettaInheritedContext.nest source))
    (result.1, outcome result.2) =
      (PettaOccurrenceOverlay.machine original .eagerValue program).run fuel source := by
  simpa only [decode, PettaInheritedContext.state_nest] using
    run_refines original program fuel (.inl (PettaInheritedContext.nest source))

theorem agrees_with_executor {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : LocalState User) :
    let result := (machine original program).run fuel (.inl source)
    (result.1, outcome result.2) = PettaInheritedContext.execute original program fuel source := by
  dsimp only
  rw [run_refines, PettaInheritedContext.execute_eq_actual]
  rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedMachine
