import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedNaturalSoundness
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedNaturalReflection
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachinePreservationExamples

/-!
# Natural Need evaluation and native admission

Independent source derivations and completed actual machine runs correspond
in both directions with exactly the same outcome and world. Every observed
bounded answer has a source derivation; an unfinished frontier is not a
refutation. These existential results do not assert a bijection of derivations,
list multiplicity, cost equality, fairness or termination.

Whole-control preservation then qualifies native values. The source typing, captured environment,
heap assignment and primitive signature are independent premises, not final
result assertions. An altered primitive still has a natural evaluation but
fails the declared dependent result judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedNaturalSemantics

open PrimeNeedReference ScopedNeedMachine
open ScopedComputation (OperationSignature)

variable {Head Operation Effect StableFault NativeFault : Type} {m n : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}

/-- Exact-world finite correspondence for independently defined evaluation.
Work and path length are existential, not claimed equal to source proof size. -/
theorem eval_iff_runSegment {origin : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} :
    Nonempty (Eval primitive origin world outcome final) ↔
      RunSegment primitive world (.run (.evaluate origin .done) []) final (.halted outcome) :=
  ⟨fun ⟨evaluation⟩ => evaluation.halts, Reflection.eval_of_runSegment⟩

theorem force_iff_runSegment {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} :
    Nonempty (Force primitive cell world outcome final) ↔
      RunSegment primitive world (.force cell []) final (.halted outcome) :=
  ⟨fun ⟨forcing⟩ => forcing.halts, Reflection.force_of_runSegment⟩

/-- Every answer actually exposed by bounded evaluation has an independent
source derivation, at the world of its reached halted state. -/
theorem answers_have_natural_derivations {origin : Closure Head Operation Effect m}
    {world : NeedWorld Head Operation Effect StableFault NativeFault m} {work : Work}
    {fuel : Nat} {outcome : Outcome Head StableFault NativeFault m}
    (member : outcome ∈ answers (spec primitive) fuel ⟨world, .run (.evaluate origin .done) [], work⟩) :
    ∃ final, Nonempty (Eval primitive origin world outcome final) := by
  obtain ⟨terminal, inFrontier, observed⟩ := List.mem_filterMap.mp member
  obtain ⟨initial, initialMember, length, _, execution⟩ := runFrontier_reachable primitive inFrontier
  cases List.mem_singleton.mp initialMember
  rcases terminal with ⟨final, control, finalWork⟩
  cases control with
  | halted result =>
      cases observed
      exact ⟨final, Reflection.eval_of_steps execution⟩
  | force _ _ | run _ _ | returned _ _ => cases observed

/-- An independently typed captured source and qualified initial heap suffice;
the final heap invariant is derived through the real execution. -/
theorem Eval.result_typing {origin : Closure Head Operation Effect m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} {types : CellTypes Head m} {A : Tm Head m}
    (evaluation : Eval primitive origin world outcome final)
    (sound : PrimitiveSoundness R signature Δ primitive)
    (source : ClosureTyping R signature Δ types origin A)
    (heap : HeapTyping R signature Δ types world.heap) : OutcomeTyping R Δ A outcome := by
  have initial : MachineTyping R signature Δ types
      (⟨world, .run (.evaluate origin .done) [], {}⟩ :
        NeedMachine Head Operation Effect StableFault NativeFault m) A :=
    ⟨heap, .run (.evaluate source (.done A)) (.nil A)⟩
  obtain ⟨length, work, path⟩ := evaluation.halts {}
  obtain ⟨finalTypes, _, admitted⟩ := steps_preservation sound path initial
  exact admitted.haltedOutcome rfl

theorem Force.result_typing {cell : CellId}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    {outcome : Outcome Head StableFault NativeFault m} {types : CellTypes Head m} {A : Tm Head m}
    (forcing : Force primitive cell world outcome final)
    (sound : PrimitiveSoundness R signature Δ primitive)
    (declared : types cell = some A)
    (heap : HeapTyping R signature Δ types world.heap) : OutcomeTyping R Δ A outcome := by
  have initial : MachineTyping R signature Δ types
      (⟨world, .force cell [], {}⟩ : NeedMachine Head Operation Effect StableFault NativeFault m) A :=
    ⟨heap, .force declared (.nil A)⟩
  obtain ⟨length, work, path⟩ := forcing.halts {}
  obtain ⟨finalTypes, _, admitted⟩ := steps_preservation sound path initial
  exact admitted.haltedOutcome rfl

/-- Loading source without external need references derives the initial
invariant from native substitution and an empty heap. -/
theorem Eval.source_value_judgment {Γ : Ctx Head n}
    {code : ScopedNeedComputation.Code Head Operation Effect n 0} {A : Tm Head n}
    {values : Sub Head n m} {value : Tm Head m}
    {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
    (evaluation : Eval primitive ⟨n, 0, code, values, Fin.elim0⟩ world (.value value) final)
    (sound : PrimitiveSoundness R signature Δ primitive)
    (source : ScopedNeedComputation.Typing R signature Γ Fin.elim0 code A)
    (environment : FormationSensitive.CtxMor R Γ Δ values)
    (context : FormationSensitive.ContextFormation R Δ)
    (empty : world.heap = Heap.empty) :
    FormationSensitive.Judgment R Δ value (subst values A) := by
  have heap : HeapTyping R signature Δ (fun _ => none) world.heap := by
    simpa only [empty] using
      (HeapTyping.empty (R := R) (signature := signature) (Δ := Δ)
        (Effect := Effect) (StableFault := StableFault))
  have captured : ClosureTyping R signature Δ (fun _ => none)
      ⟨n, 0, code, values, Fin.elim0⟩ (subst values A) :=
    .captured source environment (fun index => Fin.elim0 index)
  have admitted := evaluation.result_typing sound captured heap
  cases admitted with
  | value typed => exact ⟨context, typed⟩

namespace NativeExamples

open ScopedNeedMachine.PreservationExamples

def reflexivitySource : Closure Tower.Head ScopedNeedMachine.PreservationExamples.Operation Nat 2 :=
  ⟨2, 0, wrongSource, ids, Fin.elim0⟩

/-- The source asks for reflexivity at its actual argument. -/
def correctEvaluation : Eval ScopedNeedMachine.PreservationExamples.primitive
    reflexivitySource (initial wrongSource ids).world
    (.value (.refl newer)) (initial wrongSource ids).world :=
  .call ScopedNeedMachine.PreservationExamples.Operation.reflexivity newer ids Fin.elim0 _

theorem correct_result_judgment :
    FormationSensitive.Judgment Tower.rules context (.refl newer)
      (ScopedNeedMachine.PreservationExamples.signature.result .reflexivity newer) := by
  have environment : FormationSensitive.CtxMor Tower.rules context context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index)
  simpa only [subst_ids] using correctEvaluation.source_value_judgment
    primitive_sound wrongSource_typing environment context_formed rfl

/-- The same source also evaluates under an unqualified implementation.
Evaluation evidence alone is therefore not native proof admission. -/
def misindexedEvaluation : Eval misindexedPrimitive reflexivitySource (initial wrongSource ids).world
    (.value (.refl older)) (initial wrongSource ids).world :=
  .call ScopedNeedMachine.PreservationExamples.Operation.reflexivity newer ids Fin.elim0 _

theorem misindexed_natural_result_not_admitted :
    ¬ FormationSensitive.Judgment Tower.rules context (.refl older)
      (ScopedNeedMachine.PreservationExamples.signature.result .reflexivity newer) :=
  misindexed_return_not_admitted

theorem misindexed_natural_result_really_runs :
    RunSegment misindexedPrimitive (initial wrongSource ids).world
      (.run (.evaluate reflexivitySource .done) [])
      (initial wrongSource ids).world (.halted (.value (.refl older))) := misindexedEvaluation.halts

end NativeExamples

namespace BudgetExample

open Examples

def initial : NeedMachine Nat ExampleOperation Nat Nat Nat 0 :=
  ⟨emptyWorld, .run (.evaluate duplicateChoice .done) [], {}⟩

/-- Three actual transitions leave the selected producer unfinished. The
empty answer list coexists with a complete independent source derivation. -/
theorem unfinished_is_not_refutation :
    answers (spec Examples.primitive) 3 initial = [] ∧
      Nonempty (Eval Examples.primitive duplicateChoice emptyWorld (.value (.head 10)) leftFinal) :=
  ⟨rfl, ⟨evalLeft⟩⟩

theorem source_witness_has_completed_run :
    RunSegment Examples.primitive emptyWorld (.run (.evaluate duplicateChoice .done) [])
      leftFinal (.halted (.value (.head 10))) := evalLeft.halts

end BudgetExample

#print axioms eval_iff_runSegment
#print axioms force_iff_runSegment
#print axioms answers_have_natural_derivations
#print axioms Eval.result_typing
#print axioms Force.result_typing
#print axioms Eval.source_value_judgment
#print axioms NativeExamples.correct_result_judgment
#print axioms NativeExamples.misindexed_natural_result_not_admitted
#print axioms NativeExamples.misindexed_natural_result_really_runs
#print axioms BudgetExample.unfinished_is_not_refutation
#print axioms BudgetExample.source_witness_has_completed_run

end ScopedNeedNaturalSemantics
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
