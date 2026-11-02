import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlResultServices
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerDecode
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValuesExecution

/-! Unary negation and Boolean negation execute through the public
primitive service using the source compiler's actual argument encoding.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlUnaryPrimitives

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

private theorem variable_match (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (actual : Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    SpaceSemantics.matchValue bindings (.var name) actual =
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (.var name) actual := by
  rw [SpaceSemantics.matchValue.eq_def]

theorem negate_returns (state : State) (number : Int) :
    PureReturns runtime [] state
      (apply "gslt:ml:primitive" [encoded (InferenceCettaWire.encodePattern (primitive .negate)),
        encoded (InferenceCettaWire.encodePattern (valueList [.literal (.integer number)]))]) state
      (encoded (OCamlIntegerResult.result (-number))) := by
  have values := OCamlValuesExecution.values_returns state [.literal (.integer number)]
  have listSame : OCamlValuesExecution.valuesTerm [.literal (.integer number)] =
      encodeList id [OCamlIntegerWire.datum number] := by
    simp only [OCamlValuesExecution.valuesTerm, encodeList, value, OCamlIntegerWire.datum_exact, id_eq]
  rw [listSame] at values
  have decoded := OCamlIntegerDecode.value_returns state number
  metta_call checked
  metta_eval [values, decoded] with checked unfolding [primitive, node, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, variable_match,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList]
  apply Library.demand_call checked (head := "gslt:ml:result-integer") (by rfl) (by decide +kernel)
    _ state state state _ [integer (-number)] _ (by metta_literal; rfl)
  · apply ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-integer") (index := 0)
      (by decide +kernel) _ (.nil _ _)
    conv_rhs => rw [show -number = 0 - number by omega]
    exact integer_sub_returns _ _ state _ _ 0 number (integer_returns _ _ _ _) (bound_returns _ _ _ (by rfl))
  · exact OCamlIntegerResult.body_returns state _

theorem not_returns (state : State) (flag : Bool) :
    PureReturns runtime [] state
      (apply "gslt:ml:primitive" [encoded (InferenceCettaWire.encodePattern (primitive .notBool)),
        encoded (InferenceCettaWire.encodePattern (valueList [.literal (.boolean flag)]))]) state
      (encoded (OCamlResultServices.booleanResult (!flag))) := by
  have values := OCamlValuesExecution.values_returns state [.literal (.boolean flag)]
  metta_call checked
  cases flag <;>
    metta_eval [values] with checked unfolding [primitive, node, value, literal, OCamlValuesExecution.valuesTerm,
      InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, variable_match,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList]
  all_goals
    apply Library.demand_call checked (head := "gslt:ml:result-boolean") (by rfl) (by decide +kernel)
      _ state state state _ [_] _ (by metta_literal; rfl)
  all_goals
    first
    | exact OCamlResultServices.boolean_result_body_returns state _
    | exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-boolean") (index := 0)
        (by decide +kernel) (grounded_returns _ _ _ _) (.nil _ _)

#print axioms negate_returns
#print axioms not_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlUnaryPrimitives
