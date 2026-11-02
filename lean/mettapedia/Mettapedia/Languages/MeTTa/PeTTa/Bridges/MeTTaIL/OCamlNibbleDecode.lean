import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16NibbleExecution

/-! The full loaded service preserves the shared nibble decoder, including
its raw constructor-valued argument demand.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlNibbleDecode

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem nibble_returns (state : State) (digit : Fin 16) :
    PureReturns runtime [] state (apply "gslt:word16:nibble-value" [encoded (Word16NibbleExecution.nibble digit.val)]) state
      (encoded (.application "Some" [.natural digit.val])) := by
  have computed := Word16NibbleExecution.nibble_value_returns state digit
  metta_lift checked ["nibble"] computed

#print axioms nibble_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlNibbleDecode
