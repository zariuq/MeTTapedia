import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerResult
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerDecode
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerMultiplyExecution

/-! The loaded arithmetic helper decodes both source integers, performs
exact target arithmetic and returns the source's wrapped result encoding.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerArithmetic

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

inductive Operator where
  | add | subtract | multiply
  deriving DecidableEq

def name : Operator → String
  | .add => "MlAdd" | .subtract => "MlSubtract" | .multiply => "MlMultiply"

def compute : Operator → Int → Int → Int
  | .add => (· + ·) | .subtract => (· - ·) | .multiply => (· * ·)

theorem binary_returns (state : State) (operator : Operator) (left right : Int) :
    PureReturns runtime [] state
      (apply "gslt:ml:integer-binary" [encoded (.string (name operator)),
        encoded (OCamlIntegerWire.datum left), encoded (OCamlIntegerWire.datum right)]) state
      (encoded (OCamlIntegerResult.result (compute operator left right))) := by
  have first := OCamlIntegerDecode.value_returns state left
  have second := OCamlIntegerDecode.value_returns state right
  metta_call checked
  cases operator <;>
    metta_eval [first, second] with checked unfolding [name, compute]
  · apply Library.demand_call checked (head := "gslt:ml:result-integer") (by rfl) (by decide +kernel)
      _ state state state _ [integer (left + right)] _ (by metta_literal; rfl)
    · apply ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-integer") (index := 0)
        (by decide +kernel) _ (.nil _ _)
      apply integer_add_returns _ _ state _ _ left right
      · exact bound_returns _ _ _ (by rfl)
      · exact bound_returns _ _ _ (by rfl)
    · exact OCamlIntegerResult.body_returns state (left + right)
  · apply Library.demand_call checked (head := "gslt:ml:result-integer") (by rfl) (by decide +kernel)
      _ state state state _ [integer (left - right)] _ (by metta_literal; rfl)
    · apply ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-integer") (index := 0)
        (by decide +kernel) _ (.nil _ _)
      apply integer_sub_returns _ _ state _ _ left right
      · exact bound_returns _ _ _ (by rfl)
      · exact bound_returns _ _ _ (by rfl)
    · exact OCamlIntegerResult.body_returns state (left - right)
  · apply Library.demand_call checked (head := "gslt:ml:result-integer") (by rfl) (by decide +kernel)
      _ state state state _ [integer (left * right)] _ (by metta_literal; rfl)
    · apply ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-integer") (index := 0)
        (by decide +kernel) _ (.nil _ _)
      apply integer_mul_returns _ _ state _ _ left right
      · exact bound_returns _ _ _ (by rfl)
      · exact bound_returns _ _ _ (by rfl)
    · exact OCamlIntegerResult.body_returns state (left * right)

#print axioms binary_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerArithmetic
