import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalAdequacy
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedNaturalReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ScopedNeedMachinePreservationExamples

/-! # Finite execution and admission controls -/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedNeedNaturalSemantics
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
open NeedReference ScopedNeedMachine
open ScopedComputation (OperationSignature)
variable {Head Operation Effect StableFault NativeFault : Type} {m n : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}

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

#print axioms NativeExamples.correct_result_judgment

#print axioms NativeExamples.misindexed_natural_result_not_admitted

#print axioms NativeExamples.misindexed_natural_result_really_runs

#print axioms BudgetExample.unfinished_is_not_refutation

#print axioms BudgetExample.source_witness_has_completed_run

end ScopedNeedNaturalSemantics
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
