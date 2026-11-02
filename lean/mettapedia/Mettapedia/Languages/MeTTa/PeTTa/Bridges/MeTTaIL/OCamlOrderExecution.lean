import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScalarEqualityExecution
import Mettapedia.Languages.OCaml.Primitives
import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemandLibrary

/-! Source comparison results have an explicit runtime view. Native signed
ordering follows the actual loaded helper, independently of structural
value traversal and the final six comparison operators.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOrderExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def ordering : Ordering → Term
  | .lt => .symbol "MlLessOrder" | .eq => .symbol "MlEqualOrder" | .gt => .symbol "MlGreaterOrder"

def view : OCaml.Compared → Term
  | .error _ => .symbol "MlIncomparable"
  | .ok (.error _) => .symbol "MlFunctionalOrder"
  | .ok (.ok order) => ordering order

def integerOrder (left right : Int) : Ordering := if left < right then .lt else if left = right then .eq else .gt

theorem source_integer (left right : Int) : OCaml.compareValue (.literal (.integer left)) (.literal (.integer right)) =
    .ok (.ok (integerOrder left right)) := rfl

theorem order_body_returns (state : State) (left right : Int) :
    PureReturns runtime (Library.bind ["left", "right"] [integer left, integer right]) state
      (library.body "gslt:ml:order") state (encoded (ordering (integerOrder left right))) := by
  metta_literal
  apply pure_if_returns
  · exact integer_lt_returns _ _ state _ _ left right (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
  · by_cases less : left < right
    · simp only [less, decide_true, if_true, integerOrder, ordering]
      exact symbol_returns _ _ _ _
    · simp only [less, decide_false, integerOrder]
      apply pure_if_returns
      · exact integer_equal_returns _ _ state _ _ left right (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
      · by_cases same : left = right
        · simp only [same, decide_true, if_true, ordering]
          exact symbol_returns _ _ _ _
        · simp only [same, decide_false, if_false, ordering]
          exact symbol_returns _ _ _ _

theorem order_returns (state : State) (left right : Int) :
    PureReturns runtime [] state (apply "gslt:ml:order" [integer left, integer right]) state
      (encoded (ordering (integerOrder left right))) := by
  apply Library.demand_call checked (by rfl) (by decide +kernel) [] state state state
    [integer left, integer right] [integer left, integer right] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:order") (index := 0)
      (by decide +kernel) (integer_returns _ _ _ _)
      (.evaluated (by decide +kernel) (integer_returns _ _ _ _) (.nil _ _))
  · exact order_body_returns state left right

#print axioms source_integer
#print axioms order_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOrderExecution
