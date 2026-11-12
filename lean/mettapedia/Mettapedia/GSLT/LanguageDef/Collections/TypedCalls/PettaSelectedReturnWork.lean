import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaProducedFrameEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceChoices

/-!
# A return obligation at one physical typed-frame position

Only calls above the selected body frame belong to its running prefix. The
inherited suffix and unrelated work need not return the selected operand.
The index counts actual prefix frames, so identical frame values at different
positions do not identify their occurrences.

The predicate is a proof view of actual work. It does not change a control,
frame, binding record or execution service.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames

def Holds {User : Type} (saved : CallFrame) (argument : Atom) (index : Nat) (item : Work User) : Prop :=
  ∃ above outside, above.length = index ∧
    item.2.1.calls = above ++ saved :: outside ∧ Frames argument item.1 above

theorem at_head {User : Type} (saved : CallFrame) (argument : Atom) (item : Work User)
    (outside : List CallFrame) (calls : item.2.1.calls = saved :: outside)
    (returning : Bridges.ScopedReturnLocal.AliasHolds argument item.1) : Holds saved argument 0 item :=
  ⟨[], outside, rfl, calls, .root returning⟩

theorem selected_position {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat} {item : Work User}
    (held : Holds saved argument index item) : item.2.1.calls[index]? = some saved := by
  obtain ⟨above, outside, length, calls, _returning⟩ := held
  rw [calls, ← length]
  simp

theorem head_alias {User : Type} {saved : CallFrame} {argument : Atom} {item : Work User}
    (held : Holds saved argument 0 item) : Bridges.ScopedReturnLocal.AliasHolds argument item.1 := by
  obtain ⟨above, _outside, length, _calls, returning⟩ := held
  have empty : above = [] := List.eq_nil_of_length_eq_zero length
  subst above
  exact returning.no_calls

theorem head_observation {User : Type} {saved : CallFrame} {argument : Atom} {item : Work User}
    (held : Holds saved argument 0 item) (terminal : item.1.goals = [])
    (world : EagerDFS.World) (environment : Environment) (resolved : resolve item.1.bindings = some environment) :
    read environment item.1.destination = read environment argument := by
  exact Bridges.ScopedReturnLocal.terminal_alias_observation argument
    (⟨world, item.1, item.2.1⟩ : Cursor (Context User)) (head_alias held) terminal environment resolved

theorem protect_keeps {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat} {item : Work User}
    (held : Holds saved argument index item) (operations : Services User) (source : State User) :
    Holds saved argument index (protect operations source item.1 item.2.1, item.2) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  exact ⟨above, outside, length, calls, returning.protect operations source item.2.1⟩

/-- Actual row entry adds a prefix frame; it does not replace the selected
frame or its inherited continuation. -/
theorem row_work {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (held : Holds saved argument index (control, context, origins))
    (depth : Nat) (head : String) (arguments : List Atom) (destination : Atom)
    (older : List EagerDFS.Destination.Goal) (row : Row) (occurrence : Nat)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (ordinary : sourceOwned (.expression (.symbol head :: arguments)) = false) :
    Holds saved argument (index + 1)
      (rowWork control context origins depth head arguments destination older row occurrence) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  change context.calls = above ++ saved :: outside at calls
  let inside : Context User := {context with calls := above}
  have captured := row_work_captures_return argument control inside origins depth head arguments destination older
    row occurrence returning atCall ordinary
  refine ⟨_, outside, ?_, ?_, captured⟩
  · simp only [rowWork, inside, List.length_cons, length]
  · simp only [rowWork, inside, List.cons_append]
    rw [calls]

/-- Every newly selected body earns a mark at the current frame, without a
contract on older work or frames below it. -/
theorem selected_equations {User : Type} (program : SpaceSemantics.Program) (control : DControl)
    (boundary : Finset String) (context : Context User) (origins : List Nat)
    (saved : CallFrame) (outside : List CallFrame) (environment : Environment)
    (index inspectionFuel retained : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program saved.head index inspectionFuel = true)
    (aligned : PettaArgumentProgress.Aligned saved) (phase : saved.phase = .body)
    (within : index < saved.row.parameters.length) (target : control.destination = saved.callDestination)
    (resolved : resolve control.bindings = some environment) (calls : context.calls = saved :: outside) :
    ∃ recipe, saved.ready[index]? = some recipe ∧
      ∀ item ∈ equationWork program control boundary context origins saved.head
          (saved.ready.map (read environment)) saved.callDestination [] retained,
        Holds saved recipe 0 item := by
  obtain ⟨recipe, present, contracts⟩ := PettaProducedFrameEntry.equation_work_aliases program control boundary context
    origins saved environment index inspectionFuel retained checked aligned phase within target resolved
  refine ⟨recipe, present, ?_⟩
  intro item member
  have contract := contracts item member
  exact at_head saved recipe item outside ((congrArg Context.calls contract.1).trans calls) contract.2

/-- The actual producer run and actual equation-entry step install marked
bodies. No marked return premise is imposed on the input work or its host. -/
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
    (parameterIndex inspectionFuel : Nat) (within : parameterIndex < saved.row.parameters.length)
    (checked : Bridges.ScopedReturnFunction.checksHead program saved.head parameterIndex inspectionFuel = true) :
    ∃ recipe, saved.ready[parameterIndex]? = some recipe ∧
      let generated := equationWork program control (collectionSupport final.2) context origins saved.head
        (saved.ready.map (read environment)) saved.callDestination [] pending.length
      PettaOccurrenceOverlay.step operations .eagerValue program final =
        .silent (final.1, ⟨final.2.world, {current with frontier := generated ++ pending} :: parents⟩) ∧
      ∀ item ∈ generated, Holds saved recipe 0 item := by
  obtain ⟨recipe, present, entered, contracts⟩ := PettaProducedFrameEntry.produced_frame_entry operations program fuel
    source final good reached current parents control context origins pending saved outside environment resultName
    scopes frontier calls atCall target resolved unbound unknown notIO notCase phase parameterIndex inspectionFuel within checked
  refine ⟨recipe, present, entered, ?_⟩
  intro item member
  have contract := contracts item member
  exact at_head saved recipe item outside ((congrArg Context.calls contract.1).trans calls) contract.2

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork
