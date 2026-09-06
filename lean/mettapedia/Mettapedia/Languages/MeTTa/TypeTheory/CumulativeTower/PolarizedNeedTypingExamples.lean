import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedTyping
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputationExamples

/-!
# Native-dependent higher-order source admission

An index-dependent computation function returns native identity evidence at
its supplied argument. The function is thunked, passed to a value-level
consumer, and may be declared in a Need slot at its full computation type.
A separate source opens a native-index/closure packet and retains the native
index with the obtained evidence. These are source typing derivations, not
a claim of whole-machine preservation for the polarized runtime.

The negative controls use the actual native conversion-qualified judgment:
another index's reflexivity cannot fill the selected fibre. Value/computation
polarity and a native mathematical function versus a computation function
remain separate even when they have closely related informal descriptions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeed.Examples

variable {Operation Effect : Type} {n v k : Nat}
  {signature : ScopedComputation.OperationSignature Tower.Head Operation}
  {Γ : Tower.Ctx n} {valueTypes : Fin v → VTy Tower.Head n}
  {needTypes : Fin k → CTy Tower.Head n}

abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround
abbrev context := ScopedComputation.NativeExamples.context
abbrev older := ScopedComputation.NativeExamples.older
abbrev newer := ScopedComputation.NativeExamples.newer
abbrev operationSignature := ScopedNeedComputation.Examples.operationSignature

theorem ground_formed {n : Nat} {Γ : Tower.Ctx n} : NativeFormation Tower.rules Γ ground :=
  ⟨.sort Tower.zero, .sort Tower.zero, .headType .legacyGround⟩

def reflexiveType {n : Nat} : CTy Tower.Head n :=
  .nativePi ground (.returns (.native (.id ground (.var 0) (.var 0))))

def reflexiveFunction {n v k : Nat} : Computation Tower.Head Operation Effect n v k :=
  .nativeLambda (.returnValue (.native (.refl (.var 0))))

theorem reflexive_type_formed : ComputationFormation Tower.rules Γ reflexiveType :=
  .nativePi ground_formed (.returns (.native ⟨.sort Tower.zero, .sort Tower.zero,
    .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩))

theorem reflexive_function_typed :
    ComputationTyping (Effect := Effect) Tower.rules signature Γ valueTypes needTypes
      reflexiveFunction reflexiveType :=
  .nativeLambda ground_formed
    (.returns (.native ⟨.sort Tower.zero, .sort Tower.zero,
      .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩))
    (.returnValue (.native (.reflIntro (.var 0))))

theorem thunked_reflexive_function_typed :
    ValueTyping (Effect := Effect) Tower.rules signature Γ valueTypes needTypes
      (.thunk reflexiveFunction) (.thunk reflexiveType) :=
  .thunk reflexive_function_typed

def passedFunction {n v k : Nat} : Computation Tower.Head Operation Effect n v k :=
  .valueApply forceArgument (.thunk reflexiveFunction)

/-- The result remains a native-dependent computation function after passing
through a higher-order value-level interface. -/
theorem passed_function_typed :
    ComputationTyping (Effect := Effect) Tower.rules signature Γ valueTypes needTypes
      passedFunction reflexiveType :=
  .valueApply (forceArgument_typed reflexive_type_formed) thunked_reflexive_function_typed

theorem passed_function_application_typed {argument : Tower.Tm n}
    (admitted : FormationSensitive.Typing Tower.rules Γ argument ground) :
    ComputationTyping (Effect := Effect) Tower.rules signature Γ valueTypes needTypes
      (.nativeApply passedFunction argument)
      (.returns (.native (.id ground argument argument))) :=
  .nativeApply passed_function_typed admitted

/-- Need declarations can cache computation-function answers, not only
computations whose weak-head answer is a returned value. -/
theorem shared_function_application_typed {argument : Tower.Tm n}
    (admitted : FormationSensitive.Typing Tower.rules Γ argument ground) :
    ComputationTyping (Effect := Effect) Tower.rules signature Γ valueTypes needTypes
      (.letNeed reflexiveFunction (.nativeApply (.forceNeed 0) argument))
      (.returns (.native (.id ground argument argument))) := by
  apply ComputationTyping.letNeed reflexive_type_formed
    (.returns (.native ⟨.sort Tower.zero, .sort Tower.zero,
      .idForm (.headType .legacyGround) (.sort Tower.zero) admitted admitted⟩))
    reflexive_function_typed
  have cached : ComputationTyping (Effect := Effect) Tower.rules signature Γ valueTypes
      (extendNeedTypes reflexiveType needTypes) (.forceNeed 0) reflexiveType := .forceNeed 0
  exact .nativeApply cached admitted

def indexedType {n : Nat} : VTy Tower.Head n :=
  .sigmaNative ground (.thunk (.returns (.native (.id ground (.var 0) (.var 0)))))

def indexedThunk (index evidenceIndex : Tower.Tm n) : Value Tower.Head Operation Effect n v k :=
  .packNative index (.thunk (.returnValue (.native (.refl evidenceIndex))))

theorem indexed_thunk_formed : ValueFormation Tower.rules Γ indexedType := by
  apply ValueFormation.sigmaNative (R := Tower.rules) ground_formed
  exact .thunk (.returns (.native ⟨.sort Tower.zero, .sort Tower.zero,
    .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩))

theorem matching_indexed_thunk_typed {index : Tower.Tm n}
    (admitted : FormationSensitive.Typing Tower.rules Γ index ground) :
    ValueTyping (Effect := Effect) Tower.rules signature Γ valueTypes needTypes
      (indexedThunk index index) indexedType := by
  cases indexed_thunk_formed (Γ := Γ) with
  | sigmaNative formedA formedB =>
      apply ValueTyping.packNative formedA formedB admitted
      exact .thunk (.returnValue (.native (.reflIntro admitted)))

def retainedType {n : Nat} : VTy Tower.Head n :=
  .sigmaNative ground (.native (.id ground (.var 0) (.var 0)))

theorem retained_type_formed : ValueFormation Tower.rules Γ retainedType :=
  .sigmaNative ground_formed (.native ⟨.sort Tower.zero, .sort Tower.zero,
    .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩)

/-- Source construction is independent of its typing proof. The producer's
selected index is retained when its suspended identity evidence is consumed. -/
def retainedIndexedResult (producer : Computation Tower.Head Operation Effect n v k) :
    Computation Tower.Head Operation Effect n v k :=
  .bindValue
    (.bindNative producer
      (.returnValue (.packNative (.var 0)
        (.thunk (.returnValue (.native (.refl (.var 0))))))))
    (.unpackNative (.variable 0)
      (.bindNative (.forceThunk (.variable 0))
        (.returnValue (.packNative (.var 1) (.native (.var 0))))))

theorem retained_indexed_result_typed
    {producer : Computation Tower.Head Operation Effect n v k}
    (producerTyped : ComputationTyping Tower.rules signature Γ valueTypes needTypes
      producer (.returns (.native ground))) :
    ComputationTyping Tower.rules signature Γ valueTypes needTypes
      (retainedIndexedResult producer) (.returns retainedType) := by
  apply ComputationTyping.bindValue indexed_thunk_formed (.returns retained_type_formed)
  · apply ComputationTyping.bindNative ground_formed (.returns indexed_thunk_formed) producerTyped
    exact .returnValue (matching_indexed_thunk_typed (.var 0))
  · apply ComputationTyping.unpackNative ground_formed
      (.thunk (.returns (.native ⟨.sort Tower.zero, .sort Tower.zero,
        .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩)))
      (.returns retained_type_formed) (.variable 0)
    apply ComputationTyping.bindNative (R := Tower.rules)
      ⟨.sort Tower.zero, .sort Tower.zero,
        .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩
      (.returns retained_type_formed) (.forceThunk (.variable 0))
    apply ComputationTyping.returnValue
    apply ValueTyping.packNative ground_formed
      (.native ⟨.sort Tower.zero, .sort Tower.zero,
        .idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0)⟩) (.var 1)
    exact .native (.var 0)

theorem empty_slots_context_formed :
    ContextFormation Tower.rules context (Fin.elim0 : Fin 0 → VTy Tower.Head 2)
      (Fin.elim0 : Fin 0 → CTy Tower.Head 2) :=
  ⟨ScopedComputation.NativeExamples.context_formed,
    fun index => Fin.elim0 index, fun index => Fin.elim0 index⟩

/-- The mismatch is excluded by the native judgment including conversion
tails, not merely by comparing the syntax of two fibre expressions. -/
theorem wrong_indexed_thunk_not_typed :
    ¬ ValueTyping (Effect := Nat) Tower.rules operationSignature context Fin.elim0 Fin.elim0
      (indexedThunk newer older) indexedType := by
  intro typed
  cases typed with
  | packNative _ _ _ payload =>
      cases payload with
      | thunk body =>
          exact ScopedComputation.NativeExamples.wrong_selected_index_not_admitted body.native_return

/-- A native payload is not automatically an ordinary thunk. -/
theorem native_value_not_thunk (B : CTy Tower.Head 2) :
    ¬ ValueTyping (Effect := Nat) Tower.rules operationSignature context Fin.elim0 Fin.elim0
      (.native newer) (.thunk B) := by
  intro typed
  cases typed

/-- Returning a native mathematical function is distinct from exposing a
computation function, irrespective of the particular native term. -/
theorem returned_native_not_computation_function (term : Tower.Tm 2) :
    ¬ ComputationTyping (Effect := Nat) Tower.rules operationSignature context Fin.elim0 Fin.elim0
      (.returnValue (.native term)) reflexiveType := by
  intro typed
  cases typed

#print axioms reflexive_type_formed
#print axioms reflexive_function_typed
#print axioms thunked_reflexive_function_typed
#print axioms passed_function_typed
#print axioms passed_function_application_typed
#print axioms shared_function_application_typed
#print axioms indexed_thunk_formed
#print axioms matching_indexed_thunk_typed
#print axioms retained_type_formed
#print axioms retained_indexed_result_typed
#print axioms empty_slots_context_formed
#print axioms wrong_indexed_thunk_not_typed
#print axioms native_value_not_thunk
#print axioms returned_native_not_computation_function

end PolarizedNeed.Examples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
