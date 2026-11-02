import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValuesExecution

/-! The public division and remainder primitives consume the compiler's
operator and linked argument encodings, then run the loaded signed helper.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionPrimitive

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlSignedDivision

private theorem variable_match (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (actual : Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    SpaceSemantics.matchValue bindings (.var name) actual =
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (.var name) actual := by
  rw [SpaceSemantics.matchValue.eq_def]

theorem primitive_returns (state : State) (modulo : Bool) (left right : Int) :
    PureReturns runtime [] state
      (apply "gslt:ml:primitive"
        [encoded (InferenceCettaWire.encodePattern (primitive (OCamlDivisionSource.source modulo))),
         encoded (InferenceCettaWire.encodePattern (valueList [.literal (.integer left), .literal (.integer right)]))]) state
      (encoded (result modulo left right)) := by
  have values := OCamlValuesExecution.values_returns state [.literal (.integer left), .literal (.integer right)]
  have listSame : OCamlValuesExecution.valuesTerm [.literal (.integer left), .literal (.integer right)] =
      encodeList id [OCamlIntegerWire.datum left, OCamlIntegerWire.datum right] := by
    simp only [OCamlValuesExecution.valuesTerm, encodeList, value, OCamlIntegerWire.datum_exact, id_eq]
  rw [listSame] at values
  have division := OCamlDivisionHelper.binary_returns state modulo left right
  rw [OCamlDivisionSource.operator_exact]
  metta_call checked
  cases modulo <;>
    metta_eval [values, division] with checked unfolding [name, encodeList, variable_match,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList]

#print axioms primitive_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionPrimitive
