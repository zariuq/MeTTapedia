import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.ScopedNeedRecordedExecution

/-!
# Native admission of actually executed scoped source values

The source and execution representations remain independent of MeTTa. This
candidate-facing adapter derives a native judgment from an actual recorded
execution plus independent source, environment, heap and primitive typing.
It does not identify named TemplateScope values, first-class computation
closures, open constraints or an irreversible effect world with these values.
-/

open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.ScopedSourceExecution

open Presentation NeedReference
open ScopedNeedMachine ScopedNeedRecordedExecution ScopedNeedComputationFunction

variable {Head Operation Effect StableFault NativeFault : Type} {m n k : Nat}
  {R : Rules Head} {signature : ScopedComputation.OperationSignature Head Operation}
  {Γ : Ctx Head n} {Δ : Ctx Head m} {needTypes : Fin k → Tm Head n}
  {function : Function Head Operation Effect n k}
  {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
  {values : Sub Head n m} {needs : Fin k → CellId} {types : CellTypes Head m}
  {world final : NeedWorld Head Operation Effect StableFault NativeFault m}
  {argument value : Tm Head m} {fuel : Nat} {work : Work}

/-- Execution is recovered from the concrete compact machine; it is not
supplied as a final-value assertion in the source qualification. -/
theorem recorded_application_value_judgment
    (qualified : Qualified R signature Γ needTypes function)
    (environment : FormationSensitive.CtxMor R Γ Δ values)
    (references : ∀ index, types (needs index) = some (subst values (needTypes index)))
    (argumentTyped : FormationSensitive.Typing R Δ argument (subst values function.domain))
    (context : FormationSensitive.ContextFormation R Δ)
    (sound : PrimitiveSoundness R signature Δ primitive)
    (heap : HeapTyping R signature Δ types world.heap)
    (executed : NeedExecution.projectMachine true
      (⟨final, .halted (.value value), work⟩ : NeedMachine Head Operation Effect StableFault NativeFault m)
        ∈ recordedFrontier primitive fuel (function.open values needs argument) world) :
    FormationSensitive.Judgment R Δ value
      (inst0 argument (function.substitute values).result) := by
  obtain ⟨evaluation⟩ := eval_iff_recorded_completion.mpr ⟨fuel, work, executed⟩
  exact qualified.evaluation_value_judgment environment references argumentTyped context sound heap evaluation

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.ScopedSourceExecution
