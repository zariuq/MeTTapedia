import Mettapedia.Machines.OrderedPriorityTraversal
import Mettapedia.Machines.StoreAndDemand.FirstAnswer

/-!
# First demand over an ordered priority phase

The traversal's output is its available ordered history, not a command to
deliver that whole history again. The common first-answer client receives one
occurrence and retains the provider state. An all-error phase must close before
its first error becomes available; its other errors remain unrequested.

One provider request either observes a ready answer or performs one local
traversal transition. A missing local transition is interruption, never source
exhaustion. Request counts are not language fuel or internal host-work bounds.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedPriorityDemand

open OrderedPriorityTraversal
namespace Demand
export StoreAndDemand.FirstAnswer (Reply Result provider client start)
end Demand

variable {Work Child World Value : Type}

def poll (start : Work → Child) (next : World → Child → Option (World × Child))
    (finished : Child → Option (List Value)) (isError : Value → Bool)
    (state : State Work Child World Value) :
    Demand.Reply Value Unit × State Work Child World Value :=
  match (output isError state).head? with
  | some value => (.answer value,state)
  | none =>
      if state.control.isClosed then (.exhausted,state)
      else match tick start next finished isError state with
        | some after => (.progress,after)
        | none => (.interrupted,state)

theorem ready_answer {start : Work → Child} {next finished isError}
    {state : State Work Child World Value} {value}
    (ready : (output isError state).head? = some value) :
    poll start next finished isError state = (.answer value,state) := by
  simp [poll,ready]

theorem answer_keeps_state {start : Work → Child} {next finished isError}
    {before after : State Work Child World Value} {value}
    (answered : poll start next finished isError before = (.answer value,after)) :
    after = before ∧ (output isError before).head? = some value := by
  unfold poll at answered
  split at answered
  · cases answered; exact ⟨rfl,by assumption⟩
  · split at answered
    · cases answered
    · split at answered <;> cases answered

theorem progress_is_actual_step {start : Work → Child} {advance finished isError}
    {next : World → Child → Option (World × Child)}
    (localSound : ∀ world child reached after,
      next world child = some (reached,after) → advance world child reached after)
    {before after : State Work Child World Value}
    (progress : poll start next finished isError before = (.progress,after)) :
    ∃ rows, Step start advance finished isError before rows after := by
  unfold poll at progress
  split at progress
  · cases progress
  · split at progress
    · cases progress
    · split at progress
      · cases progress
        exact tick_sound localSound (by assumption)
      · cases progress

theorem exhaustion_requires_closed_phase {start : Work → Child} {next finished isError}
    {before after : State Work Child World Value}
    (exhausted : poll start next finished isError before = (.exhausted,after)) :
    before.control.isClosed = true ∧ after = before ∧ output isError before = [] := by
  unfold poll at exhausted
  split at exhausted
  · cases exhausted
  · split at exhausted
    · cases exhausted
      exact ⟨by assumption,rfl,List.head?_eq_none_iff.mp (by assumption)⟩
    · split at exhausted <;> cases exhausted

theorem common_client_stops_on_one_answer {start : Work → Child} {next finished isError}
    {state : State Work Child World Value} {value}
    (ready : (output isError state).head? = some value) (extra : Nat) :
    Cursor.advance (Demand.provider (poll start next finished isError))
      (Demand.client Value Unit) (fun _ _ => 1) (extra + 2)
      (Demand.start (poll start next finished isError) state) =
        (1,.done ⟨(),.answer value,state⟩) :=
  StoreAndDemand.FirstAnswer.answer_stops (poll start next finished isError)
    state state value (ready_answer ready) extra

theorem first_tick_is_progress {start : Work → Child} {next finished isError}
    {before after : State Work Child World Value}
    (computed : firstTick start next finished isError before = some after) :
    poll start next finished isError before = (.progress,after) := by
  have empty : (output isError before).isEmpty = true := by
    by_contra missing
    simp [firstTick,missing] at computed
  have advanced := firstTick_is_tick computed
  have openPhase : before.control.isClosed ≠ true := by
    intro closed
    cases shape : before.control <;> simp_all [Control.isClosed,tick]
  have head : (output isError before).head? = none :=
    List.head?_eq_none_iff.mpr (List.isEmpty_iff.mp empty)
  simp [poll,head,openPhase,advanced]

/-- A bounded traversal slice supplies the common client's genuine progress
history. This constructs the history from execution, not from an assumption
that the whole source computation terminates. -/
theorem first_slice_progress {start : Work → Child} {next finished isError}
    (fuel : Nat) (state : State Work Child World Value) :
    let result := (firstCore start next finished isError).runSlice fuel state
    StoreAndDemand.FirstAnswer.Progress (poll start next finished isError) state result.2 result.1 := by
  induction fuel generalizing state with
  | zero => exact .nil _
  | succ fuel ih =>
      cases computed : firstTick start next finished isError state with
      | none => simpa [firstCore,MachineCore.runSlice,computed] using
          StoreAndDemand.FirstAnswer.Progress.nil (next := poll start next finished isError) state
      | some after =>
          simpa [firstCore,MachineCore.runSlice,computed] using
            StoreAndDemand.FirstAnswer.Progress.step (first_tick_is_progress computed) (ih after)

/-- The existing cursor returns exactly one answer at the actual first-ready
state. Any remaining buffered errors or source work stay in that retained state. -/
theorem common_cursor_after_slice {start : Work → Child} {next finished isError}
    (fuel : Nat) (state : State Work Child World Value) (value : Value)
    (ready : (output isError ((firstCore start next finished isError).runSlice fuel state).1).head? =
      some value) :
    let result := (firstCore start next finished isError).runSlice fuel state
    Cursor.advance (Demand.provider (poll start next finished isError))
      (Demand.client Value Unit) (fun _ _ => 1) (result.2 + 2)
      (Demand.start (poll start next finished isError) state) =
        (result.2 + 1,.done ⟨(),.answer value,result.1⟩) :=
  StoreAndDemand.FirstAnswer.first_after_progress (poll start next finished isError)
    (first_slice_progress fuel state) value (ready_answer ready)

end Mettapedia.Machines.OrderedPriorityDemand
