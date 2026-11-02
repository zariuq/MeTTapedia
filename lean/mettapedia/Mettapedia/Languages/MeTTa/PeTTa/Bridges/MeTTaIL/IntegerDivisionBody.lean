import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionWrapper

/-! The public division helper's selected source body computes the same
exact result under its actual captured numeric parameters.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionBody

open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem body_returns (state : State) (number divisor : Nat) (positive : 0 < divisor) :
    PureReturns integerLibrary.runtime (Library.bind ["number", "divisor"] [WireKit.number number, WireKit.number divisor]) state
      (integerLibrary.body "gslt:integer:divmod") state
      (encoded (IntegerDivisionExecution.resultTerm (number / divisor) (number % divisor))) := by
  metta_literal
  apply pure_if_returns
  · exact natural_lt_returns _ _ state _ _ number 0
      (bound_returns _ _ _ (by rfl)) (number_returns _ _ _ _)
  · simp only [Nat.not_lt_zero, decide_false]
    apply pure_if_returns
    · exact natural_gt_returns _ _ state _ _ divisor 0
        (bound_returns _ _ _ (by rfl)) (number_returns _ _ _ _)
    · simp only [positive, decide_true, if_true]
      apply Library.demand_call integer_checked (head := "gslt:integer:divmod-positive") (by rfl) (by decide +kernel)
        _ state state state _ [WireKit.number number, WireKit.number divisor] _ (by metta_literal; rfl)
      · exact ArgumentsReturn.evaluated (program := integerLibrary.runtime)
          (head := "gslt:integer:divmod-positive") (index := 0) (by decide +kernel)
          (bound_returns _ _ _ (by rfl))
          (.evaluated (by decide +kernel) (bound_returns _ _ _ (by rfl)) (.nil _ _))
      · exact IntegerDivisionRecursive.positive_body_returns state number divisor positive

#print axioms body_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.IntegerDivisionBody
