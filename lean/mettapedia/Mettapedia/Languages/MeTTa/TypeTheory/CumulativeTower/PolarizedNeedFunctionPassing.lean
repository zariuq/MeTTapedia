import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedEvaluationEquivalence

/-!
# Passing an executable function through a value-level consumer

A higher-order caller receives an ordinary thunk of a computation function,
forces it once and applies the supplied native argument. The thunk retains
the function's original lexical environment, so this particular passage is
exact for completed outcomes and full worlds, including the function's later
allocations. It does not rewrite the captured body by source substitution.

Independent typing retains a possibly dependent result family. The raw
evaluation law also retains faults and requires neither typing nor a trusted
function answer. No memoization, equal-work law or general contextual
equivalence is inferred from passing a thunk as a value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedFunctionPassing

open PrimeNeedReference PolarizedNeedMachine PolarizedNeedNaturalSemantics
open PolarizedNeed

variable {Head Operation Effect StableFault NativeFault : Type} {n m v k : Nat}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
  {native : Sub Head n m} {values : Fin v → RuntimeValue Head Operation Effect m}
  {needs : Fin k → CellId}

def passAndApply (function : Computation Head Operation Effect n v k)
    (argument : Tm Head n) : Computation Head Operation Effect n v k :=
  .valueApply (.valueLambda (.nativeApply (.forceThunk (.variable 0)) argument)) (.thunk function)

theorem passAndApply_eval_iff (function : Computation Head Operation Effect n v k)
    (argument : Tm Head n)
    (world final : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    Nonempty (Eval primitive
      ⟨n, v, k, passAndApply function argument, native, values, needs⟩ world outcome final) ↔
      Nonempty (Eval primitive
        ⟨n, v, k, .nativeApply function argument, native, values, needs⟩ world outcome final) := by
  unfold passAndApply
  rw [valueApply_valueLambda_iff]
  constructor
  · rintro ⟨evaluation⟩
    cases evaluation with
    | nativeApply _ functionEvaluation bodyEvaluation =>
        cases functionEvaluation with
        | forceThunk _ captured original =>
            cases captured
            exact ⟨.nativeApply argument original bodyEvaluation⟩
    | nativeApplyMismatch _ functionEvaluation wrong =>
        cases functionEvaluation with
        | forceThunk _ captured original =>
            cases captured
            exact ⟨.nativeApplyMismatch argument original wrong⟩
    | nativeApplyFault _ functionEvaluation fault =>
        cases functionEvaluation with
        | forceThunk _ captured original =>
            cases captured
            exact ⟨.nativeApplyFault argument original fault⟩
        | forceThunkMismatch _ _ mismatch =>
            exact False.elim (mismatch _ _ _ _ _ _ _ rfl)
  · rintro ⟨evaluation⟩
    cases evaluation with
    | nativeApply _ functionEvaluation bodyEvaluation =>
        exact ⟨.nativeApply argument (.forceThunk (.variable 0) rfl functionEvaluation)
          bodyEvaluation⟩
    | nativeApplyMismatch _ functionEvaluation wrong =>
        exact ⟨.nativeApplyMismatch argument (.forceThunk (.variable 0) rfl functionEvaluation) wrong⟩
    | nativeApplyFault _ functionEvaluation fault =>
        exact ⟨.nativeApplyFault argument (.forceThunk (.variable 0) rfl functionEvaluation) fault⟩

theorem passAndApply_equivalent (function : Computation Head Operation Effect n v k)
    (argument : Tm Head n) :
    EvaluationEquivalent primitive
      ⟨n, v, k, passAndApply function argument, native, values, needs⟩
      ⟨n, v, k, .nativeApply function argument, native, values, needs⟩ :=
  fun world outcome final => passAndApply_eval_iff function argument world final outcome

/-- Higher-order passage also preserves execution by a later active consumer,
which may itself apply the returned computation function. -/
theorem passAndApply_runs_iff (function : Computation Head Operation Effect n v k)
    (argument : Tm Head n) (kont : Kont Head Operation Effect m)
    (world final : NeedWorld Head Operation Effect StableFault NativeFault m)
    (outcome : Outcome Head Operation Effect StableFault NativeFault m) :
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, passAndApply function argument, native, values, needs⟩ kont) [])
      final (.halted outcome) ↔
    RunSegment primitive world
      (.run (.evaluate ⟨n, v, k, .nativeApply function argument, native, values, needs⟩ kont) [])
      final (.halted outcome) :=
  (passAndApply_equivalent function argument).consumer_runs kont world outcome final

theorem passAndApply_typed {R : Rules Head}
    {signature : ScopedComputation.OperationSignature Head Operation}
    {Γ : Ctx Head n} {valueTypes : Fin v → VTy Head n} {needTypes : Fin k → CTy Head n}
    {function : Computation Head Operation Effect n v k} {argument A : Tm Head n}
    {B : CTy Head (n + 1)}
    (functionFormed : ComputationFormation R Γ (.nativePi A B))
    (resultFormed : ComputationFormation R Γ (B.instantiate argument))
    (functionTyped : ComputationTyping R signature Γ valueTypes needTypes function (.nativePi A B))
    (argumentTyped : FormationSensitive.Typing R Γ argument A) :
    ComputationTyping R signature Γ valueTypes needTypes
      (passAndApply function argument) (B.instantiate argument) :=
  .valueApply
    (.valueLambda (.thunk functionFormed) resultFormed
      (.nativeApply (.forceThunk (.variable 0)) argumentTyped))
    (.thunk functionTyped)

/-- Raw passage does not turn an ordinary native value into a computation
function. The original polarity fault and unchanged world are preserved. -/
theorem passAndApply_nonfunction (term argument : Tm Head n)
    (world : NeedWorld Head Operation Effect StableFault NativeFault m) :
    Nonempty (Eval primitive
      ⟨n, v, k, passAndApply (.returnValue (.native term)) argument, native, values, needs⟩ world
      (.retryableFault (.domain .expectedNativeFunction)) world) := by
  apply (passAndApply_eval_iff _ _ _ _ _).mpr
  exact ⟨.nativeApplyMismatch argument (.returnValue (.native term) native values needs world)
    (by intro body impossible; cases impossible)⟩

#print axioms passAndApply_eval_iff
#print axioms passAndApply_equivalent
#print axioms passAndApply_runs_iff
#print axioms passAndApply_typed
#print axioms passAndApply_nonfunction

end PolarizedNeedFunctionPassing
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
