import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValuesExecution

/-! The public primitive service consumes the compiler's actual operator
and linked values, then delegates to the proved loaded arithmetic helper.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticPrimitive

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlIntegerArithmetic

private theorem variable_match (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (actual : Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    SpaceSemantics.matchValue bindings (.var name) actual =
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (.var name) actual := by
  rw [SpaceSemantics.matchValue.eq_def]

theorem primitive_returns (state : State) (operator : Operator) (left right : Int) :
    PureReturns runtime [] state
      (apply "gslt:ml:primitive"
        [encoded (InferenceCettaWire.encodePattern (primitive (OCamlArithmeticSource.source operator))),
         encoded (InferenceCettaWire.encodePattern (valueList [.literal (.integer left), .literal (.integer right)]))]) state
      (encoded (OCamlIntegerResult.result (compute operator left right))) := by
  have values := OCamlValuesExecution.values_returns state [.literal (.integer left), .literal (.integer right)]
  have listSame : OCamlValuesExecution.valuesTerm [.literal (.integer left), .literal (.integer right)] =
      encodeList id [OCamlIntegerWire.datum left, OCamlIntegerWire.datum right] := by
    unfold OCamlValuesExecution.valuesTerm
    simp only [encodeList, value, OCamlIntegerWire.datum_exact, id_eq]
  rw [listSame] at values
  have arithmetic := binary_returns state operator left right
  rw [OCamlArithmeticSource.operator_exact]
  metta_call checked
  cases operator <;>
    metta_eval [values, arithmetic] with checked unfolding [name, encodeList, variable_match,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList]

#print axioms primitive_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticPrimitive
