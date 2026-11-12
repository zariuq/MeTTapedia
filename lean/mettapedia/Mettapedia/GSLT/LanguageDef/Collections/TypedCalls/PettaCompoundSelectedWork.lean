import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundProducedEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnFrames
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnDispatch

/-!
# Compound returns at one physical typed-frame position

The prefix is measured in the actual call stack. Its outermost caller view
carries the program-indexed compound return obligation; inherited frames
below the selected frame and unrelated work need no such obligation.

These are proof views of the existing host, not a second frame layout or
evaluator. Source entry is the maintained eager-body profile. Native body
policy realization and complete scope-mark transport remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaCompoundReturnFrames (Frames)

def Holds {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (index : Nat) (item : Work User) : Prop :=
  ∃ above outside, above.length = index ∧
    item.2.1.calls = above ++ saved :: outside ∧ Frames program argument item.1 above

theorem variable_instance {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} {item : Work User}
    (held : PettaSelectedReturnWork.Holds saved argument index item) : Holds program saved argument index item := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  exact ⟨above, outside, length, calls, PettaCompoundReturnFrames.variable_instance returning⟩

theorem at_head {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (item : Work User) (outside : List CallFrame) (calls : item.2.1.calls = saved :: outside)
    (returning : Bridges.DestinationDataReturnState.AliasHolds program argument item.1) :
    Holds program saved argument 0 item := ⟨[], outside, rfl, calls, returning⟩

theorem selected_position {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} {item : Work User} (held : Holds program saved argument index item) :
    item.2.1.calls[index]? = some saved := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  rw [calls, ← length]
  simp

theorem head_alias {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {item : Work User} (held : Holds program saved argument 0 item) :
    Bridges.DestinationDataReturnState.AliasHolds program argument item.1 := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  have empty : above = [] := List.eq_nil_of_length_eq_zero length
  subst above
  exact returning

theorem protect_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} {item : Work User} (held : Holds program saved argument index item)
    (operations : Services User) (source : State User) :
    Holds program saved argument index (protect operations source item.1 item.2.1, item.2) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  exact ⟨above, outside, length, calls, returning.protect operations source item.2.1⟩

/-- Actual callable admission is essential for compound data: a constructor
debt may not be captured as an ordinary typed prefix call. -/
theorem row_work {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (held : Holds program saved argument index (control, context, origins))
    (depth : Nat) (head : String) (arguments : List Atom) (destination : Atom)
    (older : List EagerDFS.Destination.Goal) (row : Row) (occurrence : Nat)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false)
    (called : callable program head = true) :
    Holds program saved argument (index + 1)
      (rowWork control context origins depth head arguments destination older row occurrence) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  change context.calls = above ++ saved :: outside at calls
  let inside : Context User := {context with calls := above}
  have captured := PettaCompoundReturnFrames.row_work_captures_return argument control inside origins depth head arguments
    destination older row occurrence returning atCall ordinary called
  refine ⟨_, outside, ?_, ?_, captured⟩
  · simp only [rowWork, inside, List.length_cons, length]
  · simp only [rowWork, inside, List.cons_append]
    rw [calls]

theorem local_source {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} {before after : Cursor (Context User)} (origins : List Nat)
    (source : Source.Step .eagerValue program before (.silent after))
    (held : Holds program saved argument index (before.control, before.context, origins))
    (noSequence : ∀ pairs body destination older,
      before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older) :
    Holds program saved argument index (after.control, after.context, origins) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  refine ⟨above, outside, length, ?_, ?_⟩
  · simpa only [RefinementTransport.silent_context_preserved source] using calls
  · exact PettaCompoundReturnFrames.local_source above returning noSequence source

theorem active_prefix {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} {control : DControl} {context : Context User} {origins : List Nat}
    {frame : CallFrame} {rest : List CallFrame}
    (held : Holds program saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    ∃ above outside, above.length = index ∧ rest = above ++ saved :: outside ∧
      Frames program argument control (frame :: above) := by
  obtain ⟨owned, outside, length, stack, returning⟩ := held
  change context.calls = owned ++ saved :: outside at stack
  cases owned with
  | nil => simp only [List.length_nil] at length; omega
  | cons inner above =>
      have same : frame :: rest = inner :: (above ++ saved :: outside) := calls.symm.trans stack
      obtain ⟨heads, tails⟩ := List.cons.inj same
      subst inner
      exact ⟨above, outside, by simp only [List.length_cons] at length; omega, tails, returning⟩

theorem update_inner {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (rest : List CallFrame)
    (held : Holds program saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) (after : DControl) (updated : CallFrame)
    (extended : RefinementTransport.Extends control.bindings after.bindings)
    (goals : updated.callerGoals = frame.callerGoals)
    (destination : updated.callerDestination = frame.callerDestination) :
    Holds program saved argument (index + 1) (after, {context with calls := updated :: rest}, origins) := by
  obtain ⟨above, outside, length, stack, returning⟩ := active_prefix held calls
  refine ⟨updated :: above, outside, ?_, ?_, returning.update_top extended goals destination⟩
  · simp only [List.length_cons, length]
  · simp only [List.cons_append, stack]

theorem pop_inner {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (rest : List CallFrame)
    (held : Holds program saved argument (index + 1) (control, context, origins))
    (calls : context.calls = frame :: rest) :
    Holds program saved argument index (resumeCaller control frame, {context with calls := rest}, origins) := by
  obtain ⟨above, outside, length, stack, returning⟩ := active_prefix held calls
  exact ⟨above, outside, length, stack, returning.resume_top⟩

/-- Every actual selected equation receives its own occurrence, with no
contract on the inherited suffix or the other frontier entries. -/
theorem selected_equations {User : Type} (program : SpaceSemantics.Program) (control : DControl)
    (boundary : Finset String) (context : Context User) (origins : List Nat)
    (saved : CallFrame) (outside : List CallFrame) (environment : Environment)
    (index inspectionFuel retained : Nat)
    (checked : Bridges.DestinationDataReturnFunction.checksHead program saved.head index inspectionFuel = true)
    (aligned : PettaArgumentProgress.Aligned saved) (phase : saved.phase = .body)
    (within : index < saved.row.parameters.length) (target : control.destination = saved.callDestination)
    (resolved : resolve control.bindings = some environment) (calls : context.calls = saved :: outside) :
    ∃ recipe, saved.ready[index]? = some recipe ∧
      ∀ item ∈ equationWork program control boundary context origins saved.head
          (saved.ready.map (read environment)) saved.callDestination [] retained,
        Holds program saved recipe 0 item := by
  obtain ⟨recipe, present, contracts⟩ := PettaCompoundProducedEntry.equation_work_aliases program control boundary context
    origins saved environment index inspectionFuel retained checked aligned phase within target resolved
  refine ⟨recipe, present, ?_⟩
  intro item member
  have contract := contracts item member
  exact at_head program saved recipe item outside ((congrArg Context.calls contract.1).trans calls) contract.2

/-- Operand production and actual equation entry earn the selected mark;
the input host is not assumed to carry a compound return obligation. -/
theorem source_produced_mark {User : Type} (operations : Services User)
    (program : SpaceSemantics.Program) (fuel : Nat) (source final : State User)
    (good : PettaArgumentProgress.Safe source)
    (reached : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (saved : CallFrame) (outside : List CallFrame) (environment : Environment) (resultName : String)
    (scopes : final.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = saved :: outside)
    (atCall : control.goals = [.invoke saved.head saved.ready saved.callDestination])
    (target : control.destination = saved.callDestination)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment saved.callDestination = .var resultName)
    (unknown : StdLib.known saved.head = false) (notIO : Eval.ioHead saved.head = false)
    (notCase : saved.head ≠ "case") (phase : saved.phase = .body)
    (index inspectionFuel : Nat) (within : index < saved.row.parameters.length)
    (checked : Bridges.DestinationDataReturnFunction.checksHead program saved.head index inspectionFuel = true) :
    ∃ recipe, saved.ready[index]? = some recipe ∧
      let generated := equationWork program control (collectionSupport final.2) context origins saved.head
        (saved.ready.map (read environment)) saved.callDestination [] pending.length
      PettaOccurrenceOverlay.step operations .eagerValue program final =
        .silent (final.1, ⟨final.2.world, {current with frontier := generated ++ pending} :: parents⟩) ∧
      ∀ item ∈ generated, Holds program saved recipe 0 item := by
  obtain ⟨recipe, present, entered, contracts⟩ := PettaCompoundProducedEntry.produced_frame_entry operations program fuel
    source final good reached current parents control context origins pending saved outside environment resultName
    scopes frontier calls atCall target resolved unbound unknown notIO notCase phase index inspectionFuel within checked
  refine ⟨recipe, present, entered, ?_⟩
  intro item member
  have contract := contracts item member
  exact at_head program saved recipe item outside ((congrArg Context.calls contract.1).trans calls) contract.2

theorem opening {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (held : Holds program saved argument index (control, context, origins))
    (older : List EagerDFS.Destination.Goal) (boundary : Nat) (atGoal : control.goals = .openCommit :: older) :
    Holds program saved argument index ({control with goals := older, cutBoundary := boundary}, context, origins) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  refine ⟨above, outside, length, calls, ?_⟩
  apply returning.source_step (after := {control with goals := older, cutBoundary := boundary}) (.refl _)
  rintro ⟨recipe, data, obligation⟩
  exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.open_commit_return control older boundary obligation atGoal⟩

theorem committing {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (held : Holds program saved argument index (control, context, origins))
    (older : List EagerDFS.Destination.Goal) (atGoal : control.goals = .commit :: older) :
    Holds program saved argument index ({control with goals := older}, context, origins) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  refine ⟨above, outside, length, calls, ?_⟩
  apply returning.source_step (after := {control with goals := older}) (.refl _)
  rintro ⟨recipe, data, obligation⟩
  exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.commit_return control older obligation atGoal⟩

theorem collapse_caller {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (held : Holds program saved argument index (control, context, origins))
    (child destination : Atom) (older : List EagerDFS.Destination.Goal)
    (atGoal : control.goals = .evaluate (.expression [.symbol "collapse", child]) destination :: older) :
    Holds program saved argument index ({control with goals := older}, context, origins) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  refine ⟨above, outside, length, calls, ?_⟩
  apply returning.source_step (after := {control with goals := older}) (.refl _)
  rintro ⟨recipe, data, obligation⟩
  exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.collapse_saved_return data control child destination older
    obligation atGoal⟩

/-- Copied child syntax adds a real return equation to the saved caller.
Its binding record is not replaced by a child's record or a frozen value. -/
theorem collection_copies {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (copies : List (Atom × List Atom)) (caller : CollectionCaller (Context User))
    (held : Holds program saved argument index (caller.1, caller.2.2.1, caller.2.2.2)) :
    Holds program saved argument index (Source.resumeCopies copies caller) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  refine ⟨above, outside, length, calls, ?_⟩
  apply returning.source_step (after := (Source.resumeCopies copies caller).1) (.refl _)
  rintro ⟨recipe, data, obligation⟩
  exact ⟨recipe, data, obligation.prepend_equation _ _⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork
