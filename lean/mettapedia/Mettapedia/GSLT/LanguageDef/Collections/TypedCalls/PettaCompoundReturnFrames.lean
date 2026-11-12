import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnFrames
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnState

/-!
# Compound return obligations in actual typed caller frames

The existing caller view selects the outermost owned prefix frame and keeps
the reached constraint record. Compound source obligations can use that same
view. Source steps refine its record; actual typed row entry captures the
pending return before changing the active destination. The input pattern is
not replaced by a variable or a precomputed body result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnFrames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaCallerReturnFrames (viewControl)
open Bridges.DestinationDataReturnState (AliasHolds)
open Bridges.DestinationDataRecipe (Recipe PureGoal)
open Bridges.ScopedReturnObligation (Pending AtHead)

def CallerHolds (program : SpaceSemantics.Program) (argument : Atom) (control : DControl) (frame : CallFrame) : Prop :=
  AliasHolds program argument (resumeCaller control frame)

def Frames (program : SpaceSemantics.Program) (argument : Atom) (control : DControl) (frames : List CallFrame) : Prop :=
  AliasHolds program argument (viewControl control frames)

theorem caller_refinement {program : SpaceSemantics.Program} {argument : Atom} {before after : DControl}
    (frame : CallFrame) (held : CallerHolds program argument before frame)
    (extended : RefinementTransport.Extends before.bindings after.bindings) : CallerHolds program argument after frame :=
  held.refinement extended rfl rfl

theorem caller_fields {program : SpaceSemantics.Program} {argument : Atom} {control : DControl} {before after : CallFrame}
    (held : CallerHolds program argument control before)
    (goals : after.callerGoals = before.callerGoals) (destination : after.callerDestination = before.callerDestination) :
    CallerHolds program argument control after := held.refinement (.refl _) goals destination

theorem Frames.refine_nonempty {program : SpaceSemantics.Program} {argument : Atom} {before after : DControl}
    {frames : List CallFrame} (held : Frames program argument before frames) (nonempty : frames ≠ [])
    (extended : RefinementTransport.Extends before.bindings after.bindings) : Frames program argument after frames := by
  induction frames with
  | nil => contradiction
  | cons frame frames ih =>
      cases frames with
      | nil => exact held.refinement extended rfl rfl
      | cons outer rest =>
          have retained : Frames program argument before (outer :: rest) := by
            simpa only [Frames, viewControl, List.getLast?_cons_cons] using held
          have afterHeld := ih retained (by simp)
          simpa only [Frames, viewControl, List.getLast?_cons_cons] using afterHeld

theorem Frames.push {program : SpaceSemantics.Program} {argument : Atom} {before after : DControl}
    {frames : List CallFrame} (held : Frames program argument before frames) (frame : CallFrame)
    (extended : RefinementTransport.Extends before.bindings after.bindings)
    (first : frames = [] → CallerHolds program argument after frame) :
    Frames program argument after (frame :: frames) := by
  cases frames with
  | nil => exact first rfl
  | cons outer rest =>
      simpa only [Frames, viewControl, List.getLast?_cons_cons] using held.refine_nonempty (by simp) extended

theorem Frames.update_top {program : SpaceSemantics.Program} {argument : Atom} {before after : DControl}
    {frame updated : CallFrame} {rest : List CallFrame} (held : Frames program argument before (frame :: rest))
    (extended : RefinementTransport.Extends before.bindings after.bindings)
    (goals : updated.callerGoals = frame.callerGoals)
    (destination : updated.callerDestination = frame.callerDestination) :
    Frames program argument after (updated :: rest) := by
  cases rest with
  | nil => exact caller_fields (caller_refinement frame held extended) goals destination
  | cons outer rest =>
      have retained : Frames program argument before (outer :: rest) := by
        simpa only [Frames, viewControl, List.getLast?_cons_cons] using held
      simpa only [Frames, viewControl, List.getLast?_cons_cons] using retained.refine_nonempty (by simp) extended

theorem Frames.resume_top {program : SpaceSemantics.Program} {argument : Atom} {control : DControl}
    {frame : CallFrame} {rest : List CallFrame} (held : Frames program argument control (frame :: rest)) :
    Frames program argument (resumeCaller control frame) rest := by
  cases rest with
  | nil => exact held
  | cons outer rest =>
      have retained : Frames program argument control (outer :: rest) := by
        simpa only [Frames, viewControl, List.getLast?_cons_cons] using held
      exact retained.refine_nonempty (by simp) (.refl _)

theorem Frames.protect {User : Type} {program : SpaceSemantics.Program} {argument : Atom}
    {control : DControl} {frames : List CallFrame} (held : Frames program argument control frames)
    (operations : Services User) (source : State User) (context : Context User) :
    Frames program argument (protect operations source control context) frames := by
  cases frames with
  | nil => exact held.refinement (.refl _) rfl rfl
  | cons frame rest => exact held.refine_nonempty (by simp) (.refl _)

theorem Frames.source_step {program : SpaceSemantics.Program} {argument : Atom} {before after : DControl}
    {frames : List CallFrame} (held : Frames program argument before frames)
    (extended : RefinementTransport.Extends before.bindings after.bindings)
    (ordinary : AliasHolds program argument before → AliasHolds program argument after) :
    Frames program argument after frames := by
  cases frames with
  | nil => exact ordinary held
  | cons frame rest => exact held.refine_nonempty (by simp) extended

theorem variable_instance {program : SpaceSemantics.Program} {argument : Atom} {control : DControl}
    {frames : List CallFrame} (held : PettaCallerReturnFrames.Frames argument control frames) :
    Frames program argument control frames := Bridges.DestinationDataReturnState.variable_alias_instance held.view

theorem return_expression_is_owned {recipe expression : Atom}
    (returns : Bridges.ScopedReturnSyntax.Returns recipe expression) :
    expression = recipe ∨ sourceOwned expression = true := by
  cases returns <;> simp [sourceOwned, EagerDFS.eagerControlForm]

/-- Actual callable-head admission rules out a constructor-debt head and
rules out treating the call itself as the returned data recipe. -/
theorem ordinary_call_tail {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} (data : Recipe program recipe) (control : DControl)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Bridges.DestinationDataReturnState.Holds program recipe observation control)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false)
    (called : callable program head = true) :
    Bridges.ScopedReturnLocal.Reads control.bindings control.destination observation ∨ Pending recipe control.destination older := by
  have notData : ¬ PureGoal program (.evaluate (.expression (.symbol head :: arguments)) destination) := by
    intro pure
    cases pure with
    | evaluate dataGoal =>
        exact Bridges.DestinationDataReturnState.data_recipe_is_not_a_callable dataGoal head arguments called rfl
  rcases held.outside_debt atCall notData with realized | pending
  · exact .inl realized
  · rcases pending.head_or_tail _ _ atCall with headReturn | tail
    · rcases return_expression_is_owned headReturn.2 with same | owned
      · exact (Bridges.DestinationDataReturnState.data_recipe_is_not_a_callable data head arguments called same.symm).elim
      · rw [ordinary] at owned
        cases owned
    · exact .inr tail

theorem row_work_captures_return {User : Type} {program : SpaceSemantics.Program}
    (argument : Atom) (control : DControl) (context : Context User) (origins : List Nat)
    (depth : Nat) (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (row : Row) (occurrence : Nat) (held : Frames program argument control context.calls)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false)
    (called : callable program head = true) :
    let work := rowWork control context origins depth head arguments destination older row occurrence
    Frames program argument work.1 work.2.1.calls := by
  dsimp only [rowWork]
  apply held.push (after := {control with goals := [], destination}) _ (.refl _)
  intro noCalls
  rw [noCalls] at held
  obtain ⟨recipe, data, returning⟩ := held
  refine ⟨recipe, data, returning.1, ?_⟩
  rcases ordinary_call_tail data control head arguments destination older returning atCall ordinary called with earned | pending
  · exact .inl earned
  · exact .inr (.inl pending)

theorem local_source {User : Type} {program : SpaceSemantics.Program} {argument : Atom}
    {before after : Cursor (Context User)} (frames : List CallFrame)
    (held : Frames program argument before.control frames)
    (noSequence : ∀ pairs body destination older,
      before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (source : Source.Step .eagerValue program before (.silent after)) : Frames program argument after.control frames := by
  apply held.source_step
  · exact RefinementTransport.local_step_extends source _ (by simp [RefinementTransport.localRecords])
  · exact fun ordinary => Bridges.DestinationDataReturnState.alias_silent_preserves argument ordinary noSequence source

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnFrames
