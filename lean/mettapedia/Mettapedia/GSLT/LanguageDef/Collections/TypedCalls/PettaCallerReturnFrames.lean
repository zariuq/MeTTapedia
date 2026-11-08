import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRun

/-!
# Pending body returns in nested typed caller frames

An ordinary typed call inside a recognized return body is a prefix
computation. Its saved caller retains the pending return. Further nested
calls may change the active goals and destination, but not that saved
continuation or its reached logical record. Frame occurrences are tracked by
their stack position, not by treating equal frame labels as one occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnFrames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open Bridges.ScopedReturnLocal (AliasHolds)
open Bridges.ScopedReturnObligation (Pending AtHead)

def CallerHolds (argument : Atom) (control : DControl) (frame : CallFrame) : Prop :=
  AliasHolds argument (resumeCaller control frame)

theorem caller_refinement {argument : Atom} {before after : DControl} (frame : CallFrame)
    (held : CallerHolds argument before frame)
    (extended : RefinementTransport.Extends before.bindings after.bindings) : CallerHolds argument after frame := by
  obtain ⟨name, protectedRead, returning⟩ := held
  refine ⟨name, protectedRead.extends extended, ?_⟩
  rcases returning with realized | pending
  · exact .inl (realized.extends extended)
  · exact .inr pending

theorem caller_fields {argument : Atom} {control : DControl} {before after : CallFrame}
    (held : CallerHolds argument control before)
    (goals : after.callerGoals = before.callerGoals)
    (destination : after.callerDestination = before.callerDestination) : CallerHolds argument control after := by
  simpa only [CallerHolds, AliasHolds, Bridges.ScopedReturnLocal.Holds, resumeCaller, goals, destination] using held

inductive Frames (argument : Atom) (control : DControl) : List CallFrame → Prop where
  | root (returning : AliasHolds argument control) : Frames argument control []
  | caller (frame : CallFrame) (returning : CallerHolds argument control frame) : Frames argument control [frame]
  | nested (inner outer : CallFrame) (rest : List CallFrame)
      (retained : Frames argument control (outer :: rest)) : Frames argument control (inner :: outer :: rest)

theorem Frames.no_calls {argument : Atom} {control : DControl} (held : Frames argument control []) :
    AliasHolds argument control := by cases held with | root returning => exact returning

theorem Frames.refine_nonempty {argument : Atom} {before after : DControl} {frames : List CallFrame}
    (held : Frames argument before frames) (nonempty : frames ≠ [])
    (extended : RefinementTransport.Extends before.bindings after.bindings) : Frames argument after frames := by
  induction held with
  | root => contradiction
  | caller frame returning => exact .caller frame (caller_refinement frame returning extended)
  | nested inner outer rest retained ih => exact .nested inner outer rest (ih (by simp))

theorem Frames.push {argument : Atom} {before after : DControl} {frames : List CallFrame}
    (held : Frames argument before frames) (frame : CallFrame)
    (extended : RefinementTransport.Extends before.bindings after.bindings)
    (first : frames = [] → CallerHolds argument after frame) : Frames argument after (frame :: frames) := by
  cases frames with
  | nil => exact .caller frame (first rfl)
  | cons outer rest => exact .nested frame outer rest (held.refine_nonempty (by simp) extended)

theorem Frames.update_top {argument : Atom} {before after : DControl} {frame updated : CallFrame} {rest : List CallFrame}
    (held : Frames argument before (frame :: rest))
    (extended : RefinementTransport.Extends before.bindings after.bindings)
    (goals : updated.callerGoals = frame.callerGoals)
    (destination : updated.callerDestination = frame.callerDestination) : Frames argument after (updated :: rest) := by
  cases held with
  | caller frame returning => exact .caller updated (caller_fields (caller_refinement frame returning extended) goals destination)
  | nested inner outer rest retained => exact .nested updated outer rest (retained.refine_nonempty (by simp) extended)

theorem Frames.resume_top {argument : Atom} {control : DControl} {frame : CallFrame} {rest : List CallFrame}
    (held : Frames argument control (frame :: rest)) : Frames argument (resumeCaller control frame) rest := by
  cases held with
  | caller frame returning => exact .root returning
  | nested inner outer rest retained => exact retained.refine_nonempty (by simp) (.refl _)

theorem Frames.protect {User : Type} {argument : Atom} {control : DControl} {frames : List CallFrame}
    (held : Frames argument control frames) (services : Services User) (source : State User) (context : Context User) :
    Frames argument (protect services source control context) frames := by
  cases frames with
  | nil => exact .root held.no_calls
  | cons frame rest => exact held.refine_nonempty (by simp) (.refl _)

/-- This is a proof view of the pending outer return, not another evaluator.
The actual reached binding record is used in either branch. -/
def viewControl (control : DControl) (frames : List CallFrame) : DControl :=
  match frames.getLast? with
  | none => control
  | some frame => resumeCaller control frame

theorem Frames.view {argument : Atom} {control : DControl} {frames : List CallFrame}
    (held : Frames argument control frames) : AliasHolds argument (viewControl control frames) := by
  induction held with
  | root returning => exact returning
  | caller frame returning => exact returning
  | nested inner outer rest retained ih => simpa only [viewControl, List.getLast?_cons_cons] using ih

theorem frames_of_view (argument : Atom) (control : DControl) (frames : List CallFrame)
    (held : AliasHolds argument (viewControl control frames)) : Frames argument control frames := by
  induction frames with
  | nil => exact .root held
  | cons inner rest ih =>
      cases rest with
      | nil => exact .caller inner held
      | cons outer rest => exact .nested inner outer rest (ih (by simpa only [viewControl, List.getLast?_cons_cons] using held))

theorem frames_iff_view (argument : Atom) (control : DControl) (frames : List CallFrame) :
    Frames argument control frames ↔ AliasHolds argument (viewControl control frames) :=
  ⟨Frames.view, frames_of_view argument control frames⟩

/-- Source execution keeps the typed-frame stack. When the return is saved
there, arbitrary active source work needs only record refinement. When no
typed caller is active, the actual source return theorem supplies the step. -/
theorem Frames.source_step {argument : Atom} {before after : DControl} {frames : List CallFrame}
    (held : Frames argument before frames)
    (extended : RefinementTransport.Extends before.bindings after.bindings)
    (ordinary : AliasHolds argument before → AliasHolds argument after) : Frames argument after frames := by
  cases frames with
  | nil => exact .root (ordinary held.no_calls)
  | cons frame rest => exact held.refine_nonempty (by simp) extended

theorem Frames.protect_control {argument : Atom} {control : DControl} {frames : List CallFrame}
    (held : Frames argument control frames) (boundary : Finset String) :
    Frames argument (protectControl control boundary) frames :=
  held.source_step (.refl _) (fun ordinary => ordinary)

theorem return_expression_is_owned (name : String) {expression : Atom}
    (returns : Bridges.ScopedReturnSyntax.Returns (.var name) expression) :
    expression = .var name ∨ sourceOwned expression = true := by
  cases returns <;> simp [sourceOwned, EagerDFS.eagerControlForm]

theorem ordinary_call_has_pending_caller (name : String) (control : DControl)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (pending : Pending (.var name) control.destination control.goals)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false) :
    Pending (.var name) control.destination older := by
  rcases pending.head_or_tail _ _ atCall with marked | retained
  · rcases return_expression_is_owned name marked.2 with impossible | owned
    · cases impossible
    · rw [ordinary] at owned
      cases owned
  · exact retained

theorem row_work_captures_return {User : Type} (argument : Atom) (control : DControl)
    (context : Context User) (origins : List Nat) (depth : Nat) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List EagerDFS.Destination.Goal) (row : Row) (occurrence : Nat)
    (held : Frames argument control context.calls)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false) :
    let work := rowWork control context origins depth head arguments destination older row occurrence
    Frames argument work.1 work.2.1.calls := by
  dsimp only [rowWork]
  apply held.push (after := {control with goals := [], destination}) _ (.refl _)
  intro noCalls
  rw [noCalls] at held
  obtain ⟨name, protectedRead, returning⟩ := held.no_calls
  refine ⟨name, protectedRead, ?_⟩
  rcases returning with realized | pending
  · exact .inl realized
  · exact .inr (ordinary_call_has_pending_caller name control head arguments destination older pending atCall ordinary)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnFrames
