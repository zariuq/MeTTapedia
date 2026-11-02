import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonPrimitive
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveReflection

/-! Completed public comparisons preserve and reflect the independent
source result, including the functional-comparison fault.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonAdequacy

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

theorem result_iff (state : State) (operator : OCaml.Primitive) (allowed : operator.isComparison = true)
    (left right : OCaml.Value) (expected actual : OCaml.Result)
    (evaluated : operator.eval [left, right] = .ok expected) :
    Runs runtime {state := state, control := .evaluate [] (OCamlPrimitiveReflection.call operator [left, right])}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm actual)] [] []) ↔
      operator.eval [left, right] = .ok actual := by
  have computed := OCamlComparisonPrimitive.returns state operator allowed left right
  rw [evaluated] at computed
  exact OCamlPrimitiveReflection.result_iff state operator [left, right] expected actual evaluated computed

#print axioms result_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonAdequacy
