import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16VectorExecution

/-! The loaded OCaml library preserves shared vector decoding. The
source view supplies raw capture metadata for the inherited word head.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWordDecode

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem vector_returns (state : State) (number : Nat) :
    PureReturns runtime [] state (apply "gslt:word16:vector-value" [encoded (Word16Wire.vectorTerm number)]) state
      (encoded (.application "Some" [.natural number])) := by
  apply captured_call_in_extension (Library.closed checked) (Library.agreement checked)
    [] [("vector", encoded (Word16Wire.vectorTerm number))] state state "gslt:word16:vector-value"
    [encoded (Word16Wire.vectorTerm number)] ["vector"] _
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
  · intro index argument found
    apply Or.inl
    cases index with
    | zero => decide +kernel
    | succ index => simp at found
  · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  · exact Word16VectorExecution.vector_returns state number

#print axioms vector_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWordDecode
