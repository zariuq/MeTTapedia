import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochCacheExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlInstallExecution

/-! The loaded install operation uses the exact next epoch plan and saves
the old one with its complete runner. Fresh runner initialization is a
separate common-runtime computation, with its result retained verbatim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochInstallExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlInstallExecution

theorem epoch_install_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : ProviderSnapshot) (index : Nat) (argument : OCaml.Value)
    (standard source query states receipts epochs fresh : Term)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (begun : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:runner:begin" [encoded (.symbol "ClassSearch"),
        encoded (CompletePlanWire.planTerm (epochPlan prepared (ProviderAppend.appendRows table [failureRow index argument])) [] [] (.base "MlConfig")),
        encoded standard, encoded source]) state (encoded fresh)) :
    let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let nextPlan := CompletePlanWire.planTerm (epochPlan prepared (ProviderAppend.appendRows table [failureRow index argument])) [] [] (.base "MlConfig")
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:install" [encoded oldPlan, encoded standard, encoded (doneRunner source query states receipts), encoded epochs,
        encoded (PremiseOperationsExecution.GeneralExecution.providerRowTerm (failureRow index argument))]) state
      (encoded (machine "MlRunning" nextPlan standard fresh
        (.application "LCons" [.application "MlEpoch" [oldPlan, doneRunner source query states receipts], epochs]))) := by
  apply install_returns
  · exact OCamlEpochCacheExecution.epoch_append_returns state program prepared table index argument built signatures
  · exact begun

#print axioms epoch_install_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochInstallExecution
