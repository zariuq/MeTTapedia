import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget

/-!
# A successful finite source budget bounds every actual native prefix

The local comparison rules out native stuttering. Once the executable frame
machine answers within a budget, any supplied native run from the represented
state contains at most that many events. This bound includes arbitrary native
choices of fresh occurrences and openings; it is not restricted to a selected
forward implementation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget

open Mettapedia.Languages.PartrecMachine
open FragmentsOfTheStep.TransitionMaps
open LogicOverTheStep.StepSpan (Succ)
open Interface (Frames)

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)
  {related : FrameState → State → Prop}
  (comparison : IsBisimulation Authored.frames.Step (Succ P) related)

include comparison

theorem length_le_of_answer (budget : Nat) {frame : FrameState} {state : State}
    (atFrame : related frame state) {output : List Nat}
    (answered : SourceBudget.run budget frame = .answer output) (run : P.Run state) :
    run.word.length ≤ budget := by
  induction budget generalizing frame state with
  | zero =>
      have halted := (SourceBudget.observe_answer_iff frame output).mp answered
      cases run with
      | nil => exact le_rfl
      | cons firing admitted rest =>
          have notHalted := (read_firing P comparison atFrame firing admitted).1
          rw [halted] at notHalted
          cases notHalted
  | succ budget ih =>
      cases run with
      | nil => exact Nat.zero_le _
      | cons firing admitted rest =>
          have atAfter := (read_firing P comparison atFrame firing admitted).2
          have remaining : SourceBudget.run budget (frameStep frame) = .answer output := by
            simpa only [SourceBudget.run, Function.iterate_succ_apply] using answered
          exact Nat.succ_le_succ (ih atAfter remaining rest)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget.length_le_of_answer
