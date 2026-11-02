import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureServiceExecution

/-! The loaded primitive service waits for complete empty source search,
computes a result and installs its precise row while retaining the runner.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveServiceExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlInstallExecution OCamlFailureServiceExecution

def request (operator arguments rest : Term) : Term :=
  .application "PApp" [.string "MlPrimitiveRequest", encodeList id [operator, arguments, rest]]

def rowTerm (operator arguments result : Term) : Term :=
  .application "PremiseProviderRow" [.string "ml-primitive", encodeList id [operator, arguments, result]]

theorem service_returns (state : State) (plan standard operator arguments rest result query states receipts epochs answer : Term)
    (finished : PureReturns runtime [] state
      (apply "gslt:search:status" [encoded (.symbol "ClassSearch"), encoded plan, encoded query]) state
      (encoded (.symbol "SearchComplete")))
    (empty : PureReturns runtime [] state
      (apply "gslt:search:publication" [encoded (.symbol "ClassSearch"), encoded query]) state (encoded (.symbol "LNil")))
    (computed : PureReturns runtime [] state
      (apply "gslt:ml:primitive" [encoded operator, encoded arguments]) state (encoded (.application "Some" [result])))
    (installed : PureReturns runtime [] state
      (apply "gslt:ml:install" [encoded plan, encoded standard,
        encoded (doneRunner (request operator arguments rest) query states receipts),
        encoded epochs, encoded (rowTerm operator arguments result)]) state (encoded answer)) :
    PureReturns runtime [] state
      (apply "gslt:ml:service" [encoded plan, encoded standard,
        encoded (doneRunner (request operator arguments rest) query states receipts), encoded epochs]) state
      (encoded answer) := by
  metta_call checked
  service_eval [finished, empty, computed, installed] unfolding [doneRunner, request, rowTerm, encodeList]

#print axioms service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveServiceExecution
