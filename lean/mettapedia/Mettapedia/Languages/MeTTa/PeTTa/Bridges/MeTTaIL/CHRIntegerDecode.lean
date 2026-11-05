import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRWordExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerWireExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRScalarReading

/-! The loaded CHR decoder reads compiler-produced sign-and-magnitude
values into exact target integers. No machine-width truncation is used. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRIntegerDecode

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit CHRControllerSource

def datum (value : Int) : Term := .application "PApp" [.string "ChrIntegerDigits",
  .application "LCons" [.application "PApp" [.string (if value < 0 then "ChrNegative" else "ChrNonnegative"), .symbol "LNil"],
    .application "LCons" [.application "PCollection" [.string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec",
      encodeList CHRWordExecution.nibble (Nat.digits 16 value.natAbs), .symbol "RNone"], .symbol "LNil"]]]

theorem datum_exact (value : Int) :
    InferenceCettaWire.encodePattern (ModuleFormat.CHRCompilation.integer value) = datum value := by
  simp only [ModuleFormat.CHRCompilation.integer, ModuleFormat.CHRCompilation.digits,
    InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList,
    encodeList_map, encodeList, Function.comp_def, datum]
  rfl

theorem value_returns (state : State) (value : Int) :
    PureReturns runtime [] state (apply "gslt:chr:decode-integer" [encoded (datum value)]) state
      (.expression [.symbol "Some", integer value]) := by
  have digits := CHRWordExecution.canonical_digits_value_returns state value.natAbs
  metta_call checked
  by_cases negative : value < 0
  · metta_eval [digits] with checked unfolding [datum, negative]
    apply PureData.constructor_return runtime _ state "Some" _ _ (by decide +kernel) (by decide)
    refine .cons ?_ .nil
    conv_rhs => rw [show value = 0 - (value.natAbs : Int) by rw [Int.natCast_natAbs, abs_of_neg negative]; omega]
    apply integer_sub_returns runtime _ state _ _ 0 (value.natAbs : Int)
    · exact integer_returns _ _ _ _
    · exact bound_returns _ _ _ (by rfl)
  · metta_eval [digits] with checked unfolding [datum, negative]
    apply data_returns _ _ _ _ _ (by decide +kernel)
    simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, integer, number, encoded, CettaWireAtom.encode,
      abs_of_nonneg (by omega : 0 ≤ value)]

theorem compiled_value_returns (state : State) (value : Int) :
    PureReturns runtime [] state
      (apply "gslt:chr:decode-integer"
        [encoded (InferenceCettaWire.encodePattern (ModuleFormat.CHRCompilation.integer value))]) state
      (.expression [.symbol "Some", integer value]) := by
  rw [datum_exact]
  exact value_returns state value

theorem wrong_constructor_returns_none (state : State) :
    PureReturns runtime [] state
      (apply "gslt:chr:decode-integer" [encoded (.application "Other" [])]) state (.symbol "None") := by
  metta_call checked
  metta_eval with checked

#print axioms value_returns
#print axioms compiled_value_returns
#print axioms wrong_constructor_returns_none

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRIntegerDecode
