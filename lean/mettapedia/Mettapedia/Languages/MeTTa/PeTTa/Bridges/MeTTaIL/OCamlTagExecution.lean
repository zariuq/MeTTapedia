import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWordDecode
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlScalarReading

/-! Variant type and constructor identities are decoded from the
compiler's existing unbounded canonical words, without truncation.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTagExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def tagTerm (typeId constructor : Nat) : Term := .application "PApp" [.string "MlTagNumber",
  encodeList id [Word16Wire.vectorTerm typeId, Word16Wire.vectorTerm constructor]]

theorem tag_exact (typeId constructor : Nat) : tagTerm typeId constructor =
    InferenceCettaWire.encodePattern (tag typeId constructor) := by
  simp only [tagTerm, Word16Wire.vector_exact, tag, node, digits_word, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]

theorem tag_returns (state : State) (typeId constructor : Nat) :
    PureReturns runtime [] state (apply "gslt:ml:tag-value" [encoded (tagTerm typeId constructor)]) state
      (encoded (.application "Some" [.application "MlTagValue" [.natural typeId, .natural constructor]])) := by
  have first := OCamlWordDecode.vector_returns state typeId
  have second := OCamlWordDecode.vector_returns state constructor
  metta_call checked
  metta_eval [first, second] with checked unfolding [tagTerm, encodeList]

#print axioms tag_exact
#print axioms tag_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTagExecution
