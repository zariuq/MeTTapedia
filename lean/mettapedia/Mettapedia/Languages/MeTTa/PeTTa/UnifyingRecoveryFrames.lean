import Mettapedia.Languages.MeTTa.PeTTa.DynamicRecovery

/-!
# Waiting argument frames during escaping source faults

An operand fault can be caught inside the operand or escape to its caller.
Only in the latter case is its argument waiter reached during recovery. It
discards all unfinished operand answers before visiting the caller's completed
root alternatives. Store effects and the allocation supply are not rolled back.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- No nested runtime call still handles the pending fault. This is a
condition on an observed escape boundary, not on the source language. -/
def NoCallBoundary (frames : List Frame) : Prop := Frame.dynamicCall ∉ frames

theorem recoverDynamic_outside_argument (prefixFrames caller : List Frame)
    (outside : NoCallBoundary prefixFrames) (earned : List Answer)
    (target : Eval.Target) (arguments held : List Atom) (index : Nat) :
    recoverDynamic earned (prefixFrames ++ .argument target arguments held index :: caller) =
      recoverDynamic [] caller := by
  induction prefixFrames generalizing earned with
  | nil => rfl
  | cons frame rest ih =>
      have noRest : NoCallBoundary rest := by
        intro present
        exact outside (List.mem_cons_of_mem frame present)
      cases frame with
      | dynamicCall => exact False.elim (outside List.mem_cons_self)
      | sequence pending completed => exact ih noRest (completed ++ earned)
      | _ => exact ih noRest []

/-- An escaping argument fault discards tentative operand packets and reaches
the caller's root recovery. The endpoint retains the whole reached world. -/
theorem fault_step_after_waiter (registry : SpaceSemantics.Program) (pending : Configuration)
    (reason : Effects.Fault) (faulted : pending.control = .fault reason)
    (outside : NoCallBoundary pending.frames) (caller : List Frame)
    (target : Eval.Target) (arguments held : List Atom) (index : Nat) :
    step registry {pending with
      frames := pending.frames ++ .argument target arguments held index :: caller} =
      (recoverDynamic [] caller).map fun result =>
        {pending with control := .returned result.1,frames := result.2} := by
  have erased := recoverDynamic_outside_argument pending.frames caller outside [] target arguments held index
  cases recovered : recoverDynamic [] caller <;>
    simp only [step,faulted,erased,recovered,Option.map_none,Option.map_some]

/-- An inner handler must keep its caller. Dropping a waiter across that
handler would change the continuation, even though the returned answers agree. -/
theorem inner_handler_retains_waiter (earned : List Answer) (target : Eval.Target)
    (arguments held : List Atom) (index : Nat) (caller : List Frame) :
    recoverDynamic earned (.dynamicCall :: .argument target arguments held index :: caller) =
      some (earned,.argument target arguments held index :: caller) := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
