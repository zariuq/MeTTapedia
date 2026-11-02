import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveCache
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochPlanWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource

/-! Primitive provider extension executes under the loaded service runtime
and returns the exact next epoch plan. Compiler row identities remain fixed.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveEpochCache

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem append_returns (state : State) (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : List (String × TypeExpr)) (table : ProviderSnapshot) (fields : ProviderCacheExecution.Fields)
    (signatures : table.signatures = provider.signatures)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result) :
    PureReturns runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (ProviderCacheExecution.planTerm language free [] table fields),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [primitiveRow operator arguments result])]) state
      (encoded (.application "Some" [ProviderCacheExecution.planTerm language free []
        (ProviderAppend.appendRows table [primitiveRow operator arguments result]) fields])) := by
  have base := OCamlPrimitiveCache.append_returns state language terms free table fields signatures operator arguments result
  have integer : PureReturns integerLibrary.runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (ProviderCacheExecution.planTerm language free [] table fields),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [primitiveRow operator arguments result])]) state
      (encoded (.application "Some" [ProviderCacheExecution.planTerm language free []
        (ProviderAppend.appendRows table [primitiveRow operator arguments result]) fields])) := by
    metta_lift integer_checked ["plan", "rows"] base
  have word : PureReturns wordLibrary.runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (ProviderCacheExecution.planTerm language free [] table fields),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [primitiveRow operator arguments result])]) state
      (encoded (.application "Some" [ProviderCacheExecution.planTerm language free []
        (ProviderAppend.appendRows table [primitiveRow operator arguments result]) fields])) := by
    metta_lift word_checked ["plan", "rows"] integer
  metta_lift checked ["plan", "rows"] word

theorem epoch_append_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures) :
    PureReturns runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [primitiveRow operator arguments result])]) state
      (encoded (.application "Some" [CompletePlanWire.planTerm
        (epochPlan prepared (ProviderAppend.appendRows table [primitiveRow operator arguments result])) [] [] (.base "MlConfig")])) := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  have computed := append_returns state prepared.compiled terms [] table
    (OCamlProviderPlanWire.fields (epochPlan prepared table) (.base "MlConfig")) signatures operator arguments result
  have before : ProviderCacheExecution.planTerm prepared.compiled [] [] table
      (OCamlProviderPlanWire.fields (epochPlan prepared table) (.base "MlConfig")) =
      CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig") :=
    OCamlProviderPlanWire.emitted_plan_exact (epochPlan prepared table) [] [] (.base "MlConfig")
  have after := OCamlEpochPlanWire.epoch_plan_exact prepared table
    (ProviderAppend.appendRows table [primitiveRow operator arguments result]) signatures signatures (.base "MlConfig")
  rw [before, after] at computed
  exact computed

#print axioms epoch_append_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveEpochCache
