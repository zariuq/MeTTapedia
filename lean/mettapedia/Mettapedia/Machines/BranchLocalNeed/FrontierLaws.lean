import Mettapedia.Machines.BranchLocalNeed.ReferenceSemantics

/-!
# Pointwise and batched Need frontiers

The reference machine always advances a running state. A halted state is
retained, including its world and work counters. Iterating these pointwise
frontiers agrees with the separately implemented batch frontier, whose early
exit checks whether every member is halted.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedFrontierLaws

open NeedReference

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

/-- A running instruction cannot silently disappear from the frontier. -/
theorem step_empty_iff (machine :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    step spec machine = [] ↔ isHalted machine = true := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted outcome => simp [step, isHalted]
  | force cell stack =>
      simp only [step, isHalted]
      split
      · simp
      · rename_i record present
        split
        · simp
        · simp
        · simp
        · split
          · simp
          · rename_i alternatives nonempty
            have length := branchAlternatives_length
              ({ world := world, control := .force cell stack, work := work } :
                Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
              { world with nextEvaluator := world.nextEvaluator + 1 }
              cell record world.nextEvaluator stack 0 (spec.alternatives record.origin)
            constructor
            · intro empty
              have zero := congrArg List.length empty
              rw [length] at zero
              exact (nonempty (List.length_eq_zero_iff.mp zero)).elim
            · simp
  | run localState stack | returned outcome stack =>
      simp only [step, isHalted]
      repeat' first
        | split
        | simp

theorem advance_halted (machine :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (halted : isHalted machine = true) : advance spec machine = [machine] := by
  simp [advance, (step_empty_iff spec machine).mpr halted]

theorem advance_running (machine :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (running : isHalted machine = false) : advance spec machine = step spec machine := by
  unfold advance
  split
  · have halted := (step_empty_iff spec machine).mp ‹step spec machine = []›
    simp_all
  · rfl

/-- The pointwise frontier has no batch-wide early exit. -/
def frontier : Nat →
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
    List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
  | 0, machine => [machine]
  | fuel + 1, machine => (advance spec machine).flatMap (frontier fuel)

theorem frontier_halted (fuel : Nat) (machine :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (halted : isHalted machine = true) : frontier spec fuel machine = [machine] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [frontier, advance_halted spec machine halted, ih]

theorem frontier_batch_halted (fuel : Nat) (machines :
    List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect))
    (halted : machines.all isHalted = true) :
    machines.flatMap (frontier spec fuel) = machines := by
  rw [List.all_eq_true] at halted
  induction machines with
  | nil => rfl
  | cons machine rest ih =>
      have first : isHalted machine = true := halted machine (by simp)
      have later : ∀ next ∈ rest, isHalted next = true := fun next member =>
        halted next (by simp [member])
      simp only [List.flatMap_cons, frontier_halted spec fuel machine first, ih later]
      rfl

/-- Batch evaluation and pointwise evaluation retain exactly the same worlds. -/
theorem runFrontier_eq_flatMap (fuel : Nat) (machines :
    List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    runFrontier spec fuel machines = machines.flatMap (frontier spec fuel) := by
  induction fuel generalizing machines with
  | zero => simp [runFrontier, frontier]
  | succ fuel ih =>
      simp only [runFrontier]
      split
      · exact (frontier_batch_halted spec (fuel + 1) machines ‹_›).symm
      · rw [ih]
        simp only [frontier, List.flatMap_assoc]

end Mettapedia.Machines.BranchLocalNeed.NeedFrontierLaws
