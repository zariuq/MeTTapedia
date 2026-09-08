import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedNaturalAdequacy
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedPreservationExamples

/-!
# Full-world source correspondence for shared computation functions

The existing shared-function execution supplies an actual completed machine,
not an assumed source oracle. General reflection reconstructs a natural
derivation ending in that entire world. The visible effect list is only a
projection of its full receipt graph; the heap still retains the captured
computation function.

An independent source derivation exercises ordinary thunk capture and
application in the current world. Its finite implementation exists even
though a short bounded execution has no completed answer. Neither this
absence nor a raw polarity fault is a logical refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedNaturalExamples

open PrimeNeedReference PolarizedNeedMachine PolarizedNeedNaturalSemantics
open PolarizedNeedPreservationExamples

def sampleClosure : Closure Tower.Head Unit Nat 2 :=
  ⟨2, 0, 0, sample, ids, Fin.elim0, Fin.elim0⟩

def sampleOutcome : Outcome Tower.Head Unit Nat Unit Unit 2 :=
  .value (.returned (.native (.pair (.refl PolarizedNeed.Examples.older)
    (.refl PolarizedNeed.Examples.newer))))

/-- Reflection retains exactly the observed machine world, including the
cached function and all non-effect receipts omitted by the effect projection. -/
theorem sample_natural_final_world :
    ∃ final : NeedMachine Tower.Head Unit Nat Unit Unit 2,
      final ∈ sampleFrontier 96 ∧
      haltedOutcome final = some sampleOutcome ∧
      Nonempty (Eval primitive sampleClosure (initial sample).world sampleOutcome final.world) ∧
      effects final = [3, 4, 4] ∧
      cachedFunction final = some (.nativeFunction sampleFunctionBody) := by
  have answer : sampleOutcome ∈ PrimeNeedLocalSteps.answers (extension primitive) 96 (initial sample) := by
    rw [sample_answers]
    exact List.mem_singleton_self _
  obtain ⟨final, member, observed⟩ := List.mem_filterMap.mp answer
  have evaluated := frontier_halt_has_natural_derivation primitive member observed
  have emitted : effects final ∈ (sampleFrontier 96).map effects :=
    List.mem_map.mpr ⟨final, member, rfl⟩
  rw [construction_once_calls_twice, List.mem_singleton] at emitted
  have cached : cachedFunction final ∈ (sampleFrontier 96).map cachedFunction :=
    List.mem_map.mpr ⟨final, member, rfl⟩
  rw [function_cache_retained, List.mem_singleton] at cached
  exact ⟨final, member, observed, evaluated, emitted, cached⟩

/-- Sharing construction does not share the two subsequent function calls. -/
theorem sample_calls_not_memoized
    {final : NeedMachine Tower.Head Unit Nat Unit Unit 2}
    (member : final ∈ sampleFrontier 96) : effects final ≠ [3, 4] := by
  have emitted : effects final ∈ (sampleFrontier 96).map effects :=
    List.mem_map.mpr ⟨final, member, rfl⟩
  rw [construction_once_calls_twice, List.mem_singleton] at emitted
  rw [emitted]
  intro impossible
  cases impossible

/-- The reconstructed source derivation feeds the general admission theorem;
the context, source typing and primitive qualification remain independent. -/
theorem sample_natural_native_judgment :
    FormationSensitive.Judgment Tower.rules PolarizedNeed.Examples.context
      (.pair (.refl PolarizedNeed.Examples.older) (.refl PolarizedNeed.Examples.newer))
      (resultType PolarizedNeed.Examples.older PolarizedNeed.Examples.newer) := by
  obtain ⟨final, _, _, ⟨evaluated⟩, _, _⟩ := sample_natural_final_world
  exact evaluated.native_judgment primitive_sound ScopedComputation.NativeExamples.context_formed
    (shared_initial_typed (Γ := PolarizedNeed.Examples.context) (.var 1) (.var 0))

/-- This source refutation uses the general forward path theorem and the
independently established all-fuel typing consequence, not one successful run. -/
theorem sample_no_function_polarity_derivation
    (final : NeedWorld Tower.Head Unit Nat Unit Unit 2) :
    ¬ Nonempty (Eval primitive sampleClosure (initial sample).world
      (.retryableFault (.domain .expectedNativeFunction)) final) := by
  rintro ⟨evaluated⟩
  obtain ⟨length, finalWork, path⟩ := evaluated.halts ({} : Work)
  have answer : (.retryableFault (.domain .expectedNativeFunction) :
      Outcome Tower.Head Unit Nat Unit Unit 2) ∈
      PrimeNeedLocalSteps.answers (extension primitive) length (initial sample) :=
    (PrimeNeedLocalSteps.answers_iff_steps (extension primitive) length (initial sample) _).mpr
      ⟨length, Nat.le_refl _, final, finalWork, path⟩
  exact shared_function_never_faults_on_function_polarity length answer

section Captured

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

/-- Independent source evaluation, followed by general soundness, implements
ordinary forcing and application without adding a Need cell. -/
theorem captured_thunk_halts
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (effect : Effect) (first argument : Tm Head m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world
      (.run (.evaluate (PolarizedNeedNaturalSemantics.Examples.thunkApplication effect first argument) .done) [])
      (world.record (.effect effect)).1 (.halted (.value (.returned (.native first)))) := by
  obtain ⟨evaluated⟩ := PolarizedNeedNaturalSemantics.Examples.captured_thunk_application
    primitive effect first argument world
  exact evaluated.halts

/-- A running frontier is not a source refutation: this source has a complete
independent derivation despite having no answer after its first local step. -/
theorem unfinished_is_not_refutation
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (effect : Effect) (first argument : Tm Head m)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    PrimeNeedLocalSteps.answers (extension primitive) 1
      (⟨world, .run (.evaluate
        (PolarizedNeedNaturalSemantics.Examples.thunkApplication effect first argument) .done) [], {}⟩ :
          NeedMachine Head Operation Effect StableFault NativeFault m) = [] ∧
    Nonempty (Eval primitive
      (PolarizedNeedNaturalSemantics.Examples.thunkApplication effect first argument) world
      (.value (.returned (.native first))) (world.record (.effect effect)).1) := by
  exact ⟨rfl, PolarizedNeedNaturalSemantics.Examples.captured_thunk_application
    primitive effect first argument world⟩

/-- The implemented answer is distinguished from the caller's different
argument. The effect occurs in the current world, not a stored world. -/
theorem captured_thunk_retains_older
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)
    (effect : Effect) (first argument : Tm Head m) (different : first ≠ argument)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world
      (.run (.evaluate (PolarizedNeedNaturalSemantics.Examples.thunkApplication effect first argument) .done) [])
      (world.record (.effect effect)).1 (.halted (.value (.returned (.native first)))) ∧
    (Produced.value (Answer.returned (RuntimeValue.native first)) :
      Outcome Head Operation Effect StableFault NativeFault m) ≠ .value (.returned (.native argument)) :=
  ⟨captured_thunk_halts primitive effect first argument world,
    PolarizedNeedNaturalSemantics.Examples.captured_thunk_not_argument first argument different⟩

end Captured

#print axioms sample_natural_final_world
#print axioms sample_calls_not_memoized
#print axioms sample_natural_native_judgment
#print axioms sample_no_function_polarity_derivation
#print axioms captured_thunk_halts
#print axioms unfinished_is_not_refutation
#print axioms captured_thunk_retains_older

end PolarizedNeedNaturalExamples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
