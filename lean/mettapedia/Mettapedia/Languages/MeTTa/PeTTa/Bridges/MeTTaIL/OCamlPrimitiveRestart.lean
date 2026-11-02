import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerBeginExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveInstall
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRequest

/-! Primitive installation includes actual initialization of its new
runner. Closedness and request checks follow from source encoding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveRestart

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlInstallExecution

theorem begin_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared) (resolved : continuation? (patterns program) rest = some encodedRest) :
    let source := node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest]
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:runner:begin" [encoded (.symbol "ClassSearch"),
        encoded (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (InferenceCettaWire.encodePattern source)]) state
      (encoded (CompleteExecution.classMachineTerm (epochPlan prepared table)
        (OCamlRunnerBeginExecution.begun prepared table source))) := by
  obtain ⟨closed, checked⟩ := epoch_primitive_request_checked program prepared table operator arguments rest encodedRest built resolved
  exact OCamlRunnerBeginExecution.begin_returns state prepared table _ closed checked

theorem install_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (query states receipts epochs : Term)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    let source := node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest]
    let next := ProviderAppend.appendRows table [primitiveRow operator arguments result]
    let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let nextPlan := CompletePlanWire.planTerm (epochPlan prepared next) [] [] (.base "MlConfig")
    let fresh := CompleteExecution.classMachineTerm (epochPlan prepared next)
      (OCamlRunnerBeginExecution.begun prepared next source)
    PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:install" [encoded oldPlan, encoded (OCamlEpochStandard.standard prepared),
        encoded (doneRunner (InferenceCettaWire.encodePattern source) query states receipts), encoded epochs,
        encoded (PremiseOperationsExecution.GeneralExecution.providerRowTerm (primitiveRow operator arguments result))]) state
      (encoded (machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
        (.application "LCons" [.application "MlEpoch" [oldPlan, doneRunner (InferenceCettaWire.encodePattern source) query states receipts], epochs]))) := by
  apply OCamlPrimitiveInstall.install_returns state program prepared table operator arguments result
  · exact built
  · exact signatures
  · exact begin_returns state program prepared _ operator arguments rest encodedRest built resolved

#print axioms begin_returns
#print axioms install_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveRestart
