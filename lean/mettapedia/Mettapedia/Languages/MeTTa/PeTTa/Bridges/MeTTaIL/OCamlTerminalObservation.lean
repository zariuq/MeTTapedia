import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalService
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerReadout
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlStateEncoding

/-! Source result observations are read through the controller's actual
result entry. Value and fault encodings retain the current epoch and every
earlier epoch rather than substituting a bare final value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalObservation

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

def resultPattern (result : OCaml.Result) : Pattern := match result with
  | .ok actual => node "MlDone" [value actual]
  | .error error => node "MlFault" [fault error]

theorem state_exact (pool : List OCaml.MatchPattern) (result : OCaml.Result) :
    state? pool (.halted result) = some (resultPattern result) := by cases result <;> rfl

theorem read_returns (state : State) (plan standard query states receipts epochs : Term) (result : OCaml.Result) :
    let runner := doneRunner (InferenceCettaWire.encodePattern (resultPattern result)) query states receipts
    PureReturns runtime [] state
      (apply "gslt:ml:result" [encoded (machine "MlComplete" plan standard runner epochs)]) state
      (encoded (.application "MlResult" [.symbol "MlComplete", InferenceCettaWire.encodePattern (resultPattern result),
        epochs, .application "MlEpoch" [plan, runner]])) := by
  exact OCamlControllerReadout.result_returns state (.symbol "MlComplete") plan standard (.symbol "ClassDone") _ query states receipts epochs

#print axioms state_exact
#print axioms read_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalObservation
