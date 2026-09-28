import Mettapedia.Machines.SharedContinuation
import Mettapedia.Machines.ResumableRegion

/-!
# A deterministic machine as a one-task residual program

The shared-continuation interface of `SharedContinuation` was designed around
return frames and ordered alternatives.  A deterministic machine whose whole
state is its residual (an eager rule engine between firings, for example) is
the degenerate instance: one task, no return frames, each transition a last
call with exactly one alternative, a final state published as the answer.

`iterate_residual_exact` shows that bounded execution of that program is the
machine's bounded region run (`MachineCore.runSlice`), transition for
transition, including the point where the machine stops.  So suspension and
resumption at transition boundaries, already proved for `runSlice`, are
instances of the shared residual interface and inherit its arena realization.
Interrupting inside a transition needs a finer residual; nothing here claims it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MachineCoreResidual

open SharedContinuation

variable {Term : Type}

/-- The machine as a program: control is the whole state, `Empty` frames. -/
def program (machine : MachineCore Term) :
    Program Unit machine.State machine.State Empty machine.State where
  inspect state :=
    match machine.step state with
    | some _ => .tail state
    | none => .ret state
  branches _ state :=
    match machine.step state with
    | some next => [((), next)]
    | none => []
  resume _ frame _ := frame.elim

/-- A running machine is one task with no pending returns. -/
def residual (machine : MachineCore Term) (state : machine.State) :
    State Unit machine.State Empty machine.State :=
  ⟨[⟨(), state, []⟩], []⟩

/-- A stopped machine has published its final state. -/
def stopped (machine : MachineCore Term) (state : machine.State) :
    State Unit machine.State Empty machine.State :=
  ⟨[], [((), state)]⟩

theorem step_stopped (machine : MachineCore Term) (state : machine.State) :
    step (program machine) (stopped machine state) = stopped machine state := rfl

theorem iterate_stopped (machine : MachineCore Term) (state : machine.State) (count : Nat) :
    (step (program machine))^[count] (stopped machine state) = stopped machine state := by
  induction count with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, step_stopped, ih]

/-- Bounded execution of the one-task program is exactly the bounded region
run: while the machine runs, the residual is its current state; once it stops,
its final state has been published and the frontier is empty. -/
theorem iterate_residual_exact (machine : MachineCore Term) (fuel : Nat) (state : machine.State) :
    (step (program machine))^[fuel] (residual machine state) =
      if (MachineCore.runSlice machine fuel state).2 = fuel then
        residual machine (MachineCore.runSlice machine fuel state).1
      else stopped machine (MachineCore.runSlice machine fuel state).1 := by
  induction fuel generalizing state with
  | zero => simp [MachineCore.runSlice]
  | succ fuel ih =>
      rw [Function.iterate_succ_apply]
      cases transition : machine.step state with
      | none =>
          have first : step (program machine) (residual machine state) = stopped machine state := by
            simp [step, program, residual, stopped, transition]
          rw [first, iterate_stopped]
          simp [MachineCore.runSlice, transition]
      | some next =>
          have first : step (program machine) (residual machine state) = residual machine next := by
            simp [step, program, residual, transition]
          rw [first, ih next]
          simp [MachineCore.runSlice, transition]

end Mettapedia.Machines.MachineCoreResidual
