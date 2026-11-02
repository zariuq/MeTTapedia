import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionPrimitive
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveReflection

/-! Public signed division and remainder preserve and reflect independent
source evaluation, including the ordinary zero-divisor fault.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionAdequacy

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

theorem division_iff (state : State) (modulo : Bool) (left right : Int) (actual : OCaml.Result) :
    Runs runtime {state := state, control := (.evaluate []
      (OCamlPrimitiveReflection.call (OCamlDivisionSource.source modulo) [.literal (.integer left), .literal (.integer right)]))}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm actual)] [] []) ↔
      (OCamlDivisionSource.source modulo).eval [.literal (.integer left), .literal (.integer right)] = .ok actual := by
  have computed := OCamlDivisionPrimitive.primitive_returns state modulo left right
  rw [OCamlDivisionSource.result_exact] at computed
  exact OCamlPrimitiveReflection.result_iff state _ _ _ actual (OCamlDivisionSource.source_evaluates modulo left right) computed

#print axioms division_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionAdequacy
