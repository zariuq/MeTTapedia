import Mettapedia.Machines.BranchLocalNeed.LocalStepPaths

/-!
# Actual Need execution only appends effect occurrences

The invariant is proved from the existing world instructions, then lifted to
the local-step extension. It covers every protocol operation and does not
assume that a whole execution already preserves its history.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.EffectPrefixes

open NeedReference

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type}

theorem instruction_invariant (earlier : List Effect) :
    WorldInstructionInvariant (fun world : World Origin Rule Value StableFault RetryableFault Effect =>
      earlier <+: world.receipts.effects) where
  fork _ _ present := present
  nextEvaluator _ present := present
  record world payload present _ := by
    change earlier <+: (world.receipts.append world.path payload).1.effects
    rw [ReceiptGraph.effects_append]
    exact present.trans ⟨_, rfl⟩
  cache _ _ _ _ present _ := present
  allocate _ _ _ _ _ present allocated := by
    rw [World.allocate?_effects allocated]
    exact present

theorem reference_step (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {before after : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (selected : after ∈ NeedReference.step spec before) :
    before.world.receipts.effects <+: after.world.receipts.effects :=
  step_preserves_world (instruction_invariant _) spec before after ⟨[], List.append_nil _⟩ selected

theorem local_step (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {before after : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (selected : after ∈ NeedLocalSteps.step extension before) :
    before.world.receipts.effects <+: after.world.receipts.effects := by
  cases control : before.control with
  | run localState stack =>
    cases localStep : extension.localStep localState with
    | none =>
      exact reference_step extension.reference
        (by simpa only [NeedLocalSteps.step, control, localStep] using selected)
    | some next =>
      simp only [NeedLocalSteps.step, control, localStep, List.mem_singleton] at selected
      subst after
      exact ⟨[], List.append_nil _⟩
  | force _ _ | returned _ _ | halted _ =>
    exact reference_step extension.reference
      (by simpa only [NeedLocalSteps.step, control] using selected)

theorem local_steps (extension : NeedLocalSteps.Extension Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {count : Nat} {before after : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (path : NeedLocalSteps.Steps extension count before after) :
    before.world.receipts.effects <+: after.world.receipts.effects := by
  induction path with
  | refl => exact ⟨[], List.append_nil _⟩
  | cons selected rest ih => exact (local_step extension (selected.mem extension)).trans ih

end Mettapedia.Machines.BranchLocalNeed.EffectPrefixes
