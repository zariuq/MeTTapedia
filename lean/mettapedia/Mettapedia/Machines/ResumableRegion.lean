import Mettapedia.Machines.MachineRefinement

/-!
# Bounded execution retaining its residual machine state

A finite region returns both its exact residual and the number of transitions
taken. Splitting a run does not restart it or repeat a debit. Exhausting the
region budget is not a final-state certificate. A final state may be a normal
completion or a stuck state; its observation belongs to the particular machine.

This extends `MachineCore`, independently of eager or demand-driven control.
Its unit transition count is not a claim about physical work, semantic fuel in
another language, or the latency of an individual transition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MachineCore

variable {Term OtherTerm : Type}

def runSlice (machine : MachineCore Term) : Nat → machine.State → machine.State × Nat
  | 0, state => (state, 0)
  | fuel + 1, state =>
      match machine.step state with
      | none => (state, 0)
      | some next =>
          let remaining := runSlice machine fuel next
          (remaining.1, remaining.2 + 1)

theorem runSlice_of_final (machine : MachineCore Term) (state : machine.State)
    (final : machine.step state = none) (fuel : Nat) :
    runSlice machine fuel state = (state, 0) := by
  cases fuel <;> simp [runSlice, final]

/-- Exact residual composition, with additive accounting only for transitions
actually performed. The second slice starts at the first slice's endpoint. -/
theorem runSlice_add (machine : MachineCore Term) (first second : Nat)
    (state : machine.State) :
    runSlice machine (first + second) state =
      let earlier := runSlice machine first state
      let later := runSlice machine second earlier.1
      (later.1, earlier.2 + later.2) := by
  induction first generalizing state with
  | zero => simp [runSlice]
  | succ first ih =>
      cases transition : machine.step state with
      | none => simp [Nat.succ_add, runSlice, transition,
          runSlice_of_final machine state transition]
      | some next =>
          simp only [Nat.succ_add, runSlice, transition]
          rw [ih]

theorem runSlice_used_le (machine : MachineCore Term) (fuel : Nat)
    (state : machine.State) :
    (runSlice machine fuel state).2 ≤ fuel := by
  induction fuel generalizing state with
  | zero => simp [runSlice]
  | succ fuel ih =>
      cases transition : machine.step state with
      | none => simp [runSlice, transition]
      | some next => simpa [runSlice, transition] using Nat.add_le_add_right (ih next) 1

/-- Stopping strictly before the supplied budget certifies no further step.
Using the whole budget alone cannot establish that conclusion. -/
theorem runSlice_under_budget_final (machine : MachineCore Term) (fuel : Nat)
    (state : machine.State) (early : (runSlice machine fuel state).2 < fuel) :
    machine.step (runSlice machine fuel state).1 = none := by
  induction fuel generalizing state with
  | zero => simp [runSlice] at early
  | succ fuel ih =>
      cases transition : machine.step state with
      | none => simp [runSlice, transition]
      | some next =>
          simp only [runSlice, transition] at early ⊢
          exact ih next (by omega)

/-- A decoder reflecting both successors and finality transports bounded
resumption and its transition count. Native fusion needs a region-level law
instead of this stronger single-step premise. -/
theorem runSlice_decode (source : MachineCore Term) (target : MachineCore OtherTerm)
    (decode : target.State → source.State)
    (step_exact : ∀ state,
      (target.step state).map decode = source.step (decode state))
    (fuel : Nat) (state : target.State) :
    (decode (runSlice target fuel state).1, (runSlice target fuel state).2) =
      runSlice source fuel (decode state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      have exactStep := step_exact state
      cases transition : target.step state with
      | none =>
          simp only [transition, Option.map_none] at exactStep
          simp [runSlice, transition, ← exactStep]
      | some next =>
          simp only [transition, Option.map_some] at exactStep
          simp only [runSlice, transition, ← exactStep]
          have exactRun := ih next
          have states := congrArg Prod.fst exactRun
          have counts := congrArg Prod.snd exactRun
          exact Prod.ext states (congrArg (· + 1) counts)

end Mettapedia.Machines.MachineCore
