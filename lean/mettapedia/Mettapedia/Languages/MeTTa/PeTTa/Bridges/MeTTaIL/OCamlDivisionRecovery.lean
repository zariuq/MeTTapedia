import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlResultServices
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScalarEqualityExecution

/-! Signed quotient and remainder recovery composes the actual conditional
expressions with the loaded integer-result service.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionRecovery

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def quotientCode : Atom := .expression [.symbol "if", apply "==" [.var "negativeFirst", .var "negativeSecond"],
  .var "quotient", apply "-" [integer 0, .var "quotient"]]
def remainderCode : Atom := .expression [.symbol "if", .var "negativeFirst",
  apply "-" [integer 0, .var "remainder"], .var "remainder"]

theorem quotient_returns (state : State) (caller : Subst) (first second : Bool) (quotient : Nat)
    (firstRead : caller.lookup "negativeFirst" = some (Effects.boolean first))
    (secondRead : caller.lookup "negativeSecond" = some (Effects.boolean second))
    (quotientRead : caller.lookup "quotient" = some (number quotient)) :
    PureReturns runtime caller state (apply "gslt:ml:result-integer" [quotientCode]) state
      (encoded (OCamlIntegerResult.result (if first = second then (quotient : Int) else -(quotient : Int)))) := by
  apply Library.demand_call checked (head := "gslt:ml:result-integer") (by rfl) (by decide +kernel)
    caller state state state _ [integer (if first = second then (quotient : Int) else -(quotient : Int))] _
    (by metta_literal; rfl)
  · apply ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-integer") (index := 0)
      (by decide +kernel) _ (.nil _ _)
    apply pure_if_returns
    · exact boolean_equal_returns _ _ state _ _ first second (bound_returns _ _ _ firstRead) (bound_returns _ _ _ secondRead)
    · by_cases same : first = second
      · simp only [same, decide_true, if_true]
        exact bound_returns _ _ _ quotientRead
      · simp only [same, decide_false]
        conv_rhs => rw [show -(quotient : Int) = 0 - (quotient : Int) by omega]
        exact integer_sub_returns _ _ state _ _ 0 quotient (integer_returns _ _ _ _) (bound_returns _ _ _ quotientRead)
  · exact OCamlIntegerResult.body_returns state _

theorem remainder_returns (state : State) (caller : Subst) (negative : Bool) (remainder : Nat)
    (flagRead : caller.lookup "negativeFirst" = some (Effects.boolean negative))
    (remainderRead : caller.lookup "remainder" = some (number remainder)) :
    PureReturns runtime caller state (apply "gslt:ml:result-integer" [remainderCode]) state
      (encoded (OCamlIntegerResult.result (if negative then -(remainder : Int) else (remainder : Int)))) := by
  apply Library.demand_call checked (head := "gslt:ml:result-integer") (by rfl) (by decide +kernel)
    caller state state state _ [integer (if negative then -(remainder : Int) else (remainder : Int))] _
    (by metta_literal; rfl)
  · apply ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-integer") (index := 0)
      (by decide +kernel) _ (.nil _ _)
    apply pure_if_returns
    · exact bound_returns _ _ _ flagRead
    · cases negative with
      | false => exact bound_returns _ _ _ remainderRead
      | true =>
        conv_rhs => rw [show -(remainder : Int) = 0 - (remainder : Int) by omega]
        exact integer_sub_returns _ _ state _ _ 0 remainder (integer_returns _ _ _ _) (bound_returns _ _ _ remainderRead)
  · exact OCamlIntegerResult.body_returns state _

#print axioms quotient_returns
#print axioms remainder_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionRecovery
