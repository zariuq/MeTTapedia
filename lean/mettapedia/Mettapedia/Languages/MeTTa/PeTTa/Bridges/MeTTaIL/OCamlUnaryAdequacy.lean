import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlUnaryPrimitives
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveReflection

/-! Public unary primitive observations preserve and reflect the independent
source evaluation result, including wrapped negation at the minimum integer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlUnaryAdequacy

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

theorem negate_iff (state : State) (number : Int) (actual : OCaml.Result) :
    Runs runtime {state := state, control := .evaluate [] (OCamlPrimitiveReflection.call .negate [.literal (.integer number)])}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm actual)] [] []) ↔
      OCaml.Primitive.eval .negate [.literal (.integer number)] = .ok actual := by
  have computed := OCamlUnaryPrimitives.negate_returns state number
  rw [OCamlIntegerResult.result_exact] at computed
  exact OCamlPrimitiveReflection.result_iff state .negate [.literal (.integer number)] _ actual rfl computed

theorem not_iff (state : State) (flag : Bool) (actual : OCaml.Result) :
    Runs runtime {state := state, control := .evaluate [] (OCamlPrimitiveReflection.call .notBool [.literal (.boolean flag)])}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm actual)] [] []) ↔
      OCaml.Primitive.eval .notBool [.literal (.boolean flag)] = .ok actual := by
  have computed := OCamlUnaryPrimitives.not_returns state flag
  rw [OCamlResultServices.boolean_result_exact] at computed
  exact OCamlPrimitiveReflection.result_iff state .notBool [.literal (.boolean flag)] _ actual rfl computed

#print axioms negate_iff
#print axioms not_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlUnaryAdequacy
