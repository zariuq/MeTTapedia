import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalLocalReflection
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalActionReflection
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalProtocolReflection

/-!
# Completed first-class machine runs supply independent source derivations

Each actual transition reconstructs the independent meaning of its predecessor.
Backward induction starts at a halted machine, not at an assumed source
derivation or a typing invariant. The result retains the exact final world.

Only completed finite paths are covered. Neither global termination nor a
bijection counting duplicated derivations follows from this existence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalSemantics
namespace Reflection

open PrimeNeedReference PolarizedNeedMachine

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

theorem step_backward
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    {machine next : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (member : next ∈ PrimeNeedLocalSteps.step (extension primitive) machine)
    (meaning : ControlMeaning primitive next.control next.world outcome final) :
    ControlMeaning primitive machine.control machine.world outcome final := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted result => simp only [PrimeNeedLocalSteps.step, step, List.not_mem_nil] at member
  | force cell stack => exact force_step_backward primitive world work cell stack member meaning
  | returned result stack => exact returned_step_backward primitive world work result stack member meaning
  | run state stack =>
      cases selected : localStep state with
      | some successor =>
          simp only [PrimeNeedLocalSteps.step, extension, selected, List.mem_singleton] at member
          subst next
          rcases meaning with ⟨result, completed, evaluated, remaining⟩
          exact ⟨result, completed, local_meaning_backward selected evaluated, remaining⟩
      | none =>
          have fallback : next ∈ step (reference primitive) ⟨world, .run state stack, work⟩ := by
            simpa only [PrimeNeedLocalSteps.step, extension, selected] using member
          cases state with
          | evaluate closure kont =>
              exact evaluate_fallback_backward primitive world work closure kont stack selected fallback meaning
          | complete result =>
              simp only [step, reference, action, List.mem_singleton] at fallback
              subst next
              exact ⟨result, world, ⟨rfl, rfl⟩, meaning⟩
          | demand cell resume =>
              simp only [step, reference, action, List.mem_singleton] at fallback
              subst next
              rcases meaning with ⟨input, selected, forced, result, completed, resumed, remaining⟩
              exact ⟨result, completed, ⟨input, selected, forced, resumed⟩, remaining⟩

theorem steps_backward
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {length : Nat} {initial terminal : NeedMachine Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (execution : PrimeNeedLocalSteps.Steps (extension primitive) length initial terminal)
    (meaning : ControlMeaning primitive terminal.control terminal.world outcome final) :
    ControlMeaning primitive initial.control initial.world outcome final := by
  induction execution with
  | refl => exact meaning
  | cons occurrence rest ih =>
      exact step_backward primitive (occurrence.mem (extension primitive)) (ih meaning)

theorem eval_of_steps
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {length : Nat} {work finalWork : Work}
    (execution : PrimeNeedLocalSteps.Steps (extension primitive) length
      ⟨world, .run (.evaluate closure .done) [], work⟩ ⟨final, .halted outcome, finalWork⟩) :
    Nonempty (Eval primitive closure world outcome final) := by
  have meaning := steps_backward execution (show ControlMeaning primitive (.halted outcome) final
    outcome final from ⟨rfl, rfl⟩)
  rcases meaning with ⟨result, selected, evaluated, rfl, rfl⟩
  exact eval_done_meaning.mp evaluated

theorem force_of_steps
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {cell : CellId} {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    {length : Nat} {work finalWork : Work}
    (execution : PrimeNeedLocalSteps.Steps (extension primitive) length
      ⟨world, .force cell [], work⟩ ⟨final, .halted outcome, finalWork⟩) :
    Nonempty (Force primitive cell world outcome final) := by
  have meaning := steps_backward execution (show ControlMeaning primitive (.halted outcome) final
    outcome final from ⟨rfl, rfl⟩)
  rcases meaning with ⟨result, selected, forced, rfl, rfl⟩
  exact forced

theorem eval_of_runSegment
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {closure : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (execution : RunSegment primitive world (.run (.evaluate closure .done) []) final (.halted outcome)) :
    Nonempty (Eval primitive closure world outcome final) := by
  obtain ⟨length, finalWork, path⟩ := execution {}
  exact eval_of_steps path

theorem force_of_runSegment
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {cell : CellId} {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (execution : RunSegment primitive world (.force cell []) final (.halted outcome)) :
    Nonempty (Force primitive cell world outcome final) := by
  obtain ⟨length, finalWork, path⟩ := execution {}
  exact force_of_steps path

/-- A cached computation function, thunk or native packet cannot be replaced
by another answer by any completed finite force path. -/
theorem no_cached_other_halt
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    {cell : CellId} {origin : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {answer other : Answer Head Operation Effect m} {length : Nat} {work finalWork : Work}
    (cached : world.heap.lookup cell = some ⟨origin, .value answer⟩) (different : other ≠ answer) :
    ¬ PrimeNeedLocalSteps.Steps (extension primitive) length ⟨world, .force cell [], work⟩
      ⟨final, .halted (.value other), finalWork⟩ := by
  intro execution
  obtain ⟨derived⟩ := force_of_steps execution
  have same := (derived.cachedValue_exact cached).1
  exact different (Produced.value.inj same)

#print axioms step_backward
#print axioms steps_backward
#print axioms eval_of_steps
#print axioms force_of_steps
#print axioms eval_of_runSegment
#print axioms force_of_runSegment
#print axioms no_cached_other_halt

end Reflection
end PolarizedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
