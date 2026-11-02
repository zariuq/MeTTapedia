import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlNibbleDecode
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.NumericMultiplyExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlScalarReading

/-! The existing byte decoder combines the compiler's two bounded nibbles
using exact target arithmetic. This helper is shared with string comparison.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlByteExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def byteTerm (byte : UInt8) : Term := .application "PApp" [.string "MlByteValue",
  encodeList id [Word16NibbleExecution.nibble (byte.toNat / 16), Word16NibbleExecution.nibble (byte.toNat % 16)]]

theorem byte_exact (byte : UInt8) : byteTerm byte = InferenceCettaWire.encodePattern (byteCode byte) := by
  simp only [byteTerm, byteCode, node, Word16NibbleExecution.nibble, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]

theorem byte_returns (state : State) (byte : UInt8) :
    PureReturns runtime [] state (apply "gslt:ml:byte-value" [encoded (byteTerm byte)]) state
      (encoded (.application "Some" [.natural byte.toNat])) := by
  have high : byte.toNat / 16 < 16 := by have bounded : byte.toNat < 256 := byte.toNat_lt_size; omega
  have first := OCamlNibbleDecode.nibble_returns state ⟨byte.toNat / 16, high⟩
  have second := OCamlNibbleDecode.nibble_returns state ⟨byte.toNat % 16, Nat.mod_lt _ (by decide)⟩
  metta_call checked
  metta_eval [first, second] with checked unfolding [byteTerm, encodeList]
  apply pure_let_returns _ _ _ "number" _ (number byte.toNat) _ _ (by rfl)
  · have joined : 16 * (byte.toNat / 16) + byte.toNat % 16 = byte.toNat := by omega
    conv_rhs => rw [← joined]
    apply natural_add_returns
    · apply natural_mul_returns
      · exact number_returns _ _ _ _
      · exact bound_returns _ _ _ (by rfl)
    · exact bound_returns _ _ _ (by rfl)
  · metta_eval with checked

#print axioms byte_exact
#print axioms byte_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlByteExecution
