import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlInstallExecution

/-! The controller's actual result reader retains all earlier epochs and
the complete current plan/runner pair.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerReadout

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlInstallExecution

theorem result_returns (state : State) (phase plan standard status source query states receipts epochs : Term) :
    let runner := Term.application "ClassMachine" [status, source, query, states, receipts]
    PureReturns runtime [] state
      (apply "gslt:ml:result" [encoded (.application "MlMachine" [phase, plan, standard, runner, epochs])]) state
      (encoded (.application "MlResult" [phase, source, epochs, .application "MlEpoch" [plan, runner]])) := by
  metta_call checked
  metta_eval with checked

#print axioms result_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerReadout
