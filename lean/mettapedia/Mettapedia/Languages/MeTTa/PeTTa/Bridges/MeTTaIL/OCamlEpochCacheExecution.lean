import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAuthorizedCacheExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochPlanWire

/-! A loaded table append returns the exact plan wire for the next epoch,
not merely an unclassified tuple of preserved metadata fields.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochCacheExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit

theorem epoch_append_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (argument : OCaml.Value)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures) :
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [failureRow index argument])]) state
      (encoded (.application "Some" [CompletePlanWire.planTerm
        (epochPlan prepared (ProviderAppend.appendRows table [failureRow index argument])) [] [] (.base "MlConfig")])) := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  have computed := OCamlFailureInstall.append_returns state prepared.compiled terms [] table
    (OCamlProviderPlanWire.fields (epochPlan prepared table) (.base "MlConfig")) signatures index argument
  have before : ProviderCacheExecution.planTerm prepared.compiled [] [] table
      (OCamlProviderPlanWire.fields (epochPlan prepared table) (.base "MlConfig")) =
      CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig") :=
    OCamlProviderPlanWire.emitted_plan_exact (epochPlan prepared table) [] [] (.base "MlConfig")
  have after : ProviderCacheExecution.planTerm prepared.compiled [] []
      (ProviderAppend.appendRows table [failureRow index argument])
      (OCamlProviderPlanWire.fields (epochPlan prepared table) (.base "MlConfig")) =
      CompletePlanWire.planTerm (epochPlan prepared (ProviderAppend.appendRows table [failureRow index argument])) [] [] (.base "MlConfig") :=
    OCamlEpochPlanWire.epoch_plan_exact prepared table (ProviderAppend.appendRows table [failureRow index argument])
      signatures signatures (.base "MlConfig")
  rw [before, after] at computed
  exact computed

#print axioms epoch_append_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochCacheExecution
