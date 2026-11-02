import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerEncode
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlWrapExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveReturn

/-! The loaded integer-result service wraps, encodes and tags the exact
source primitive result using the existing compact IR.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerResult

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def result (number : Int) : Term := .application "Some"
  [.application "PApp" [.string "MlPrimitiveValue", encodeList id [OCamlIntegerWire.datum (OCaml.wrapInteger number)]]]

theorem result_exact (number : Int) : result number = .application "Some"
    [InferenceCettaWire.encodePattern (OCamlCompilation.primitiveResult (.ok (.literal (.integer (OCaml.wrapInteger number)))))] := by
  unfold result
  rw [OCamlIntegerWire.datum_exact]
  simp only [OCamlCompilation.primitiveResult, OCamlCompilation.node, OCamlCompilation.value,
    InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]
  rfl

theorem body_returns (state : State) (number : Int) :
    PureReturns runtime (Library.bind ["number"] [integer number]) state (library.body "gslt:ml:result-integer") state
      (encoded (result number)) := by
  metta_literal
  apply pure_let_star_returns _ _ _ _ _ _ _ rfl
  apply pure_let_returns _ _ _ "wrapped" _ (integer (OCaml.wrapInteger number)) _ _ (by rfl)
  · apply Library.demand_call checked (head := "gslt:ml:wrap") (by rfl) (by decide +kernel)
      _ state state state _ [integer number] _ (by metta_literal; rfl)
    · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:wrap") (index := 0)
        (by decide +kernel) (bound_returns _ _ _ (by rfl)) (.nil _ _)
    · exact OCamlWrapExecution.wrap_body_returns state number
  · apply pure_let_returns _ _ _ "value" _ (encoded (OCamlIntegerWire.datum (OCaml.wrapInteger number))) _ _ (by rfl)
    · apply Library.demand_call checked (head := "gslt:ml:integer") (by rfl) (by decide +kernel)
        _ state state state _ [integer (OCaml.wrapInteger number)] _ (by metta_literal; rfl)
      · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:integer") (index := 0)
          (by decide +kernel) (bound_returns _ _ _ (by rfl)) (.nil _ _)
      · exact OCamlIntegerEncode.body_returns state (OCaml.wrapInteger number)
    · have packed := pack1_returns state "MlPrimitiveValue" (OCamlIntegerWire.datum (OCaml.wrapInteger number))
      metta_eval [packed] with checked unfolding [result]

theorem result_returns (state : State) (number : Int) :
    PureReturns runtime [] state (apply "gslt:ml:result-integer" [integer number]) state (encoded (result number)) := by
  apply Library.demand_call checked (by rfl) (by decide +kernel) [] state state state
    [integer number] [integer number] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-integer") (index := 0)
      (by decide +kernel) (integer_returns _ _ _ _) (.nil _ _)
  · exact body_returns state number

#print axioms result_exact
#print axioms result_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerResult
