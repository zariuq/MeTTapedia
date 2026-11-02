import Mettapedia.Machines.ResumableRegion

/-! Finality and completion transfer through exact retained slices. -/

set_option autoImplicit false

namespace Mettapedia.Machines.MachineCore

variable {Term : Type}

theorem runSlice_after_final (machine : MachineCore Term) (first second : Nat) (state : machine.State)
    (stopped : machine.step (machine.runSlice first state).1 = none) :
    machine.runSlice (first + second) state = machine.runSlice first state := by
  rw [runSlice_add]
  dsimp only
  rw [runSlice_of_final machine _ stopped]
  simp

theorem runSlice_terminal_unique (machine : MachineCore Term) (first second : Nat) (state : machine.State)
    (left : machine.step (machine.runSlice first state).1 = none)
    (right : machine.step (machine.runSlice second state).1 = none) :
    machine.runSlice first state = machine.runSlice second state := by
  have one := runSlice_after_final machine first second state left
  have two := runSlice_after_final machine second first state right
  rw [Nat.add_comm second first] at two
  exact one.symm.trans two

theorem runSlice_residual_completes (machine : MachineCore Term) (whole earlierBudget : Nat) (state : machine.State)
    (stopped : machine.step (machine.runSlice whole state).1 = none) :
    (machine.runSlice whole (machine.runSlice earlierBudget state).1).1 = (machine.runSlice whole state).1 ∧
      (machine.runSlice earlierBudget state).2 + (machine.runSlice whole (machine.runSlice earlierBudget state).1).2 =
        (machine.runSlice whole state).2 := by
  have final := runSlice_after_final machine whole earlierBudget state stopped
  rw [Nat.add_comm whole earlierBudget, runSlice_add] at final
  have endpoint := congrArg (fun page : machine.State × Nat => page.1) final
  have debit := congrArg (fun page : machine.State × Nat => page.2) final
  exact ⟨endpoint, debit⟩

theorem runSlice_larger_final (machine : MachineCore Term) (first second : Nat) (state : machine.State)
    (stopped : machine.step (machine.runSlice first state).1 = none) (enough : first ≤ second) :
    machine.runSlice second state = machine.runSlice first state := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  exact runSlice_after_final machine first extra state stopped

end Mettapedia.Machines.MachineCore
