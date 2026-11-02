import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveEpochCache
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlInstallExecution

/-! Primitive cache installation retains the previous exact plan and
runner before restarting at the same request under the extended table.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveInstall

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlInstallExecution

theorem install_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (standard source query states receipts epochs fresh : Term)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (begun : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:runner:begin" [encoded (.symbol "ClassSearch"),
        encoded (CompletePlanWire.planTerm (epochPlan prepared
          (ProviderAppend.appendRows table [primitiveRow operator arguments result])) [] [] (.base "MlConfig")),
        encoded standard, encoded source]) state (encoded fresh)) :
    let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let nextPlan := CompletePlanWire.planTerm (epochPlan prepared
      (ProviderAppend.appendRows table [primitiveRow operator arguments result])) [] [] (.base "MlConfig")
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:install" [encoded oldPlan, encoded standard, encoded (doneRunner source query states receipts), encoded epochs,
        encoded (PremiseOperationsExecution.GeneralExecution.providerRowTerm (primitiveRow operator arguments result))]) state
      (encoded (machine "MlRunning" nextPlan standard fresh
        (.application "LCons" [.application "MlEpoch" [oldPlan, doneRunner source query states receipts], epochs]))) := by
  apply OCamlInstallExecution.install_returns
  · exact OCamlPrimitiveEpochCache.epoch_append_returns state program prepared table operator arguments result built signatures
  · exact begun

#print axioms install_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveInstall
