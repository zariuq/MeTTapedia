import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareBytes
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValueWireShapes

/-! The already-supported string value shape delegates to the existing
lexicographic byte service. Source-string frontend admission is separate.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareStringValues

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution

theorem returns (state : State) (left right : List UInt8) :
    PureReturns runtime [] state (apply "gslt:ml:compare"
      [encoded (valueTerm (.literal (.string left))), encoded (valueTerm (.literal (.string right)))]) state
      (encoded (view (OCaml.compareValue (.literal (.string left)) (.literal (.string right))))) := by
  have bytes := OCamlCompareBytes.bytes_returns state left right
  metta_call checked
  ml_compare_eval [bytes] unfolding [OCamlValueWireShapes.string_exact, OCamlCompareBytes.bytesTerm, encodeList]

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareStringValues
