import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16CanonicalDecode

/-! The vector wrapper uses the compiler's exact collection tag and
closed-rest marker before delegating to the shared digit decoder.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16VectorExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem vector_returns (state : State) (number : Nat) :
    PureReturns wordLibrary.runtime [] state
      (apply "gslt:word16:vector-value" [encoded (Word16Wire.vectorTerm number)]) state
      (encoded (.application "Some" [.natural number])) := by
  have digits := Word16CanonicalDecode.value_returns state number
  metta_call word_checked
  metta_eval [digits] with word_checked unfolding [Word16Wire.vectorTerm]

theorem wrong_wrapper_returns (state : State) :
    PureReturns wordLibrary.runtime [] state
      (apply "gslt:word16:vector-value" [encoded (.application "PCollection" [.string "bag", .symbol "LNil", .symbol "RNone"])]) state
      (encoded (.symbol "None")) := by
  metta_call word_checked
  metta_eval with word_checked

#print axioms vector_returns
#print axioms wrong_wrapper_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16VectorExecution
