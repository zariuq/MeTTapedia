import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSignedDivision

/-! The complete loaded binary division helper selects its actual signed
branch after decoding both compiler integer values.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionHelper

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlSignedDivision

theorem binary_returns (state : State) (modulo : Bool) (left right : Int) :
    PureReturns runtime [] state
      (apply "gslt:ml:integer-binary" [encoded (.string (name modulo)),
        encoded (OCamlIntegerWire.datum left), encoded (OCamlIntegerWire.datum right)]) state
      (encoded (result modulo left right)) := by
  have first := OCamlIntegerDecode.value_returns state left
  have second := OCamlIntegerDecode.value_returns state right
  metta_call checked
  cases modulo <;> metta_eval [first, second] with checked unfolding [name]
  · convert (branch_returns state false left right) using 1 <;> rfl
  · convert (branch_returns state true left right) using 1 <;> rfl

#print axioms binary_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionHelper
