import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerDecode
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlResultServices

/-! Scalar and functional-prefix branches execute the actual common
comparison source. Integer comparison reuses the proved decoder and order
helper rather than inspecting or comparing the physical digit sequence.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareScalars

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution

theorem integer_returns (state : State) (left right : Int) :
    PureReturns runtime [] state
      (apply "gslt:ml:compare" [encoded (OCamlIntegerWire.datum left), encoded (OCamlIntegerWire.datum right)]) state
      (encoded (ordering (integerOrder left right))) := by
  have first := OCamlIntegerDecode.value_returns state left
  have second := OCamlIntegerDecode.value_returns state right
  metta_call checked
  ml_compare_eval [first, second] unfolding [OCamlIntegerWire.datum, encodeList]
  apply Library.demand_call checked (head := "gslt:ml:order") (by rfl) (by decide +kernel)
    _ state state state _ [integer left, integer right] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:order") (index := 0)
      (by decide +kernel) (bound_returns _ _ _ (by rfl))
      (.evaluated (by decide +kernel) (bound_returns _ _ _ (by rfl)) (.nil _ _))
  · exact order_body_returns state left right

theorem boolean_returns (state : State) (left right : Bool) :
    PureReturns runtime [] state
      (apply "gslt:ml:compare" [encoded (OCamlResultServices.booleanTerm left), encoded (OCamlResultServices.booleanTerm right)]) state
      (encoded (view (OCaml.compareValue (.literal (.boolean left)) (.literal (.boolean right))))) := by
  cases left <;> cases right <;> metta_call checked <;>
    ml_compare_eval [] unfolding [OCamlResultServices.booleanTerm, OCaml.compareValue, view, ordering]

theorem unit_returns (state : State) :
    PureReturns runtime [] state (apply "gslt:ml:compare" [encoded (valueTerm (.literal .unit)), encoded (valueTerm (.literal .unit))]) state
      (encoded (.symbol "MlEqualOrder")) := by
  metta_call checked
  ml_compare_eval [] unfolding [valueTerm, value, literal, node, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

theorem nil_returns (state : State) :
    PureReturns runtime [] state (apply "gslt:ml:compare" [encoded (valueTerm (.literal .nil)), encoded (valueTerm (.literal .nil))]) state
      (encoded (.symbol "MlEqualOrder")) := by
  metta_call checked
  ml_compare_eval [] unfolding [valueTerm, value, literal, node, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

theorem functional_left_returns (state : State) (fields other : Term) :
    PureReturns runtime [] state (apply "gslt:ml:compare" [encoded (.application "PApp" [.string "MlClosure", fields]), encoded other]) state
      (encoded (.symbol "MlFunctionalOrder")) := by
  metta_call checked
  ml_compare_eval [] unfolding []

#print axioms integer_returns
#print axioms boolean_returns
#print axioms functional_left_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareScalars
