import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueReading

/-! The loaded service reads the compiler's linked value list without
changing order, duplicates or the values' syntax.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValuesExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def valuesTerm (items : List OCaml.Value) : Term :=
  encodeList (fun actual => InferenceCettaWire.encodePattern (value actual)) items

theorem values_returns (state : State) (items : List OCaml.Value) :
    PureReturns runtime [] state
      (apply "gslt:ml:values" [encoded (InferenceCettaWire.encodePattern (valueList items))]) state
      (encoded (.application "Some" [valuesTerm items])) := by
  induction items with
  | nil => metta_call checked; metta_eval with checked unfolding [valueList, node, valuesTerm, encodeList, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList]
  | cons first rest ih =>
    metta_call checked
    metta_eval [ih] with checked unfolding [valueList, node, valuesTerm, encodeList, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList]

#print axioms values_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValuesExecution
