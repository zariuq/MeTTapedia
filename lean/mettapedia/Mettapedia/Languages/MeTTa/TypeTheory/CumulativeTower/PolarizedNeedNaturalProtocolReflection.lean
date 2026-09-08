import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalMeaning

/-!
# Backward source reconstruction through first-class Need protocol steps

Forcing reconstructs an independent cached, missing, evaluating, or suspended
source rule from the actual successor. In the suspended case the selected
source occurrence and its body evaluation are recovered from that successor's
meaning, then finalized at the original owner. Return frames reconstruct
source resumption or exact owned finalization.

These proofs assume meaning only for the successor, not a source evaluation
of the predecessor. They preserve complete worlds and arbitrary outer stacks.
Local source execution and the finite-path induction are separate proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics
namespace Reflection

open PrimeNeedReference PolarizedNeedMachine

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

theorem force_step_backward
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) (work : Work)
    (cell : CellId) (stack : List (Frame (Resume Head Operation Effect m)))
    {next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (member : next ∈ PrimeNeedLocalSteps.step (extension primitive) ⟨world, .force cell stack, work⟩)
    (meaning : ControlMeaning primitive next.control next.world outcome final) :
    ControlMeaning primitive (.force cell stack) world outcome final := by
  cases present : world.heap.lookup cell with
  | none =>
      simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, present, List.mem_singleton] at member
      subst next
      exact ⟨_, _, ⟨.missing present⟩, meaning⟩
  | some record =>
      rcases record with ⟨origin, cache⟩
      cases cache with
      | value answer =>
          simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, present, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨.cachedValue present⟩, meaning⟩
      | stableFault fault =>
          simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, present, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨.cachedStable present⟩, meaning⟩
      | evaluating owner =>
          simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, present, List.mem_singleton] at member
          subst next
          exact ⟨_, _, ⟨.evaluating present⟩, meaning⟩
      | suspended =>
          obtain ⟨position, rule, selected, ⟨selection⟩, entered, control⟩ :=
            force_suspended_successor primitive rfl present member
          rw [control, entered] at meaning
          rcases meaning with ⟨bodyOutcome, bodyFinal, evaluated, remaining⟩
          obtain ⟨evaluation⟩ := eval_done_meaning.mp evaluated
          exact ⟨_, _, ⟨.suspended present selection evaluation⟩, remaining⟩

theorem returned_step_backward
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) (work : Work)
    (result : Outcome Head Operation Effect StableFault NativeFault m)
    (stack : List (Frame (Resume Head Operation Effect m)))
    {next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (member : next ∈ PrimeNeedLocalSteps.step (extension primitive) ⟨world, .returned result stack, work⟩)
    (meaning : ControlMeaning primitive next.control next.world outcome final) :
    ControlMeaning primitive (.returned result stack) world outcome final := by
  cases stack with
  | nil =>
      simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, List.mem_singleton] at member
      subst next
      exact meaning
  | cons frame rest =>
      cases frame with
      | resume token =>
          simp only [PrimeNeedLocalSteps.step, PrimeNeedReference.step, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨resumed, selected, resumedMeaning, remaining⟩
          exact ⟨resumed, selected,
            (afterDemand_meaning primitive token result world resumed selected).mp resumedMeaning, remaining⟩
      | commit cell owner =>
          obtain ⟨completed, returned⟩ := finalize_successor primitive rfl member
          rw [returned, completed] at meaning
          exact meaning

/-- A genuine cached answer supplies source meaning without being recomputed,
including when the answer is a computation function. -/
theorem cached_value_meaning
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {world : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {answer : Answer Head Operation Effect m}
    (cached : world.heap.lookup cell = some ⟨origin, .value answer⟩) :
    ControlMeaning primitive (.force cell []) world (.value answer)
      (world.record (.observe cell (.value answer))).1 :=
  ⟨_, _, ⟨.cachedValue cached⟩, rfl, rfl⟩

/-- Neither another answer nor a changed final world can be supplied as the
meaning of a completed-cache force. -/
theorem cached_value_meaning_exact
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {cell : CellId} {origin : Closure Head Operation Effect m} {answer : Answer Head Operation Effect m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (cached : world.heap.lookup cell = some ⟨origin, .value answer⟩)
    (meaning : ControlMeaning primitive (.force cell []) world outcome final) :
    outcome = .value answer ∧ final = (world.record (.observe cell (.value answer))).1 := by
  rcases meaning with ⟨result, selected, ⟨forcing⟩, rfl, rfl⟩
  exact forcing.cachedValue_exact cached

#print axioms force_step_backward
#print axioms returned_step_backward
#print axioms cached_value_meaning
#print axioms cached_value_meaning_exact

end Reflection
end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
