import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWordDecode
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWireExecution

/-! The loaded signed integer decoder reads the compact IR's existing
sign-and-magnitude values into exact target integers.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerDecode

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit OCamlControllerSource

theorem value_returns (state : State) (number : Int) :
    PureReturns runtime [] state (apply "gslt:ml:integer-value" [encoded (OCamlIntegerWire.datum number)]) state
      (.expression [.symbol "Some", integer number]) := by
  have word := OCamlWordDecode.vector_returns state number.natAbs
  metta_call checked
  by_cases negative : number < 0
  · metta_eval [word] with checked unfolding [OCamlIntegerWire.datum, OCamlIntegerWire.sign, negative]
    apply pure_let_returns _ _ _ "number" _ (integer number) _ _ (by rfl)
    · conv_rhs => rw [show number = 0 - |number| by rw [abs_of_neg negative]; omega]
      apply integer_sub_returns _ _ state _ _ 0 |number|
      · exact integer_returns _ _ _ _
      · exact bound_returns _ _ _ (by rfl)
    · apply data_returns _ _ _ _ _ (by decide +kernel)
      simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  · metta_eval [word] with checked unfolding [OCamlIntegerWire.datum, OCamlIntegerWire.sign, negative]
    apply data_returns _ _ _ _ _ (by decide +kernel)
    simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, integer, abs_of_nonneg (by omega : 0 ≤ number)]

#print axioms value_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerDecode
