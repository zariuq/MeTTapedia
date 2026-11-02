import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlResultServices

/-! All six comparison operators share the same loaded result formatter.
Functional comparison remains a fault; an incomparable pair remains a
refusal rather than a Boolean answer.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonFormatter

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution

def supported : OCaml.Primitive → Bool
  | .equal | .different | .less | .lessEqual | .greater | .greaterEqual => true
  | _ => false

def name (operator : OCaml.Primitive) : String := match primitive operator with
  | .apply label [] => label
  | _ => ""

theorem operator_exact (operator : OCaml.Primitive) :
    InferenceCettaWire.encodePattern (primitive operator) = .application "PApp" [.string (name operator), .symbol "LNil"] := by
  cases operator <;> simp only [name, primitive, node, InferenceCettaWire.encodePattern,
    InferenceCettaWire.encodePatterns_eq_encodeList, encodeList]

private theorem result_at (state : State) (caller : Subst) (code : Atom) (flag : Bool)
    (computed : PureReturns runtime caller state code state (Effects.boolean flag)) :
    PureReturns runtime caller state (apply "gslt:ml:result-boolean" [code]) state
      (encoded (OCamlResultServices.booleanResult flag)) := by
  apply Library.demand_call checked (head := "gslt:ml:result-boolean") (by rfl) (by decide +kernel)
    caller state state state [code] [Effects.boolean flag] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-boolean") (index := 0)
      (by decide +kernel) computed (.nil _ _)
  · exact OCamlResultServices.boolean_result_body_returns state flag

private theorem order_equal (state : State) (caller : Subst) (left : Atom) (order other : Ordering)
    (returned : PureReturns runtime caller state left state (encoded (ordering order))) :
    PureReturns runtime caller state (apply "==" [left, encoded (ordering other)]) state
      (Effects.boolean (decide (order = other))) := by
  have compared := term_equal_returns runtime caller state left (encoded (ordering other)) (ordering order) (ordering other)
    returned (by cases other <;> exact symbol_returns _ _ _ _)
  have same : (ordering order = ordering other) ↔ order = other := by cases order <;> cases other <;> simp [ordering]
  simpa only [same] using compared

theorem comparison_returns (state : State) (operator : OCaml.Primitive) (allowed : supported operator = true) (order : Ordering) :
    PureReturns runtime [] state (apply "gslt:ml:comparison" [encoded (.string (name operator)), encoded (ordering order)]) state
      (encoded (OCamlResultServices.booleanResult (OCaml.comparison operator order))) := by
  cases operator <;> simp [supported] at allowed
  all_goals cases order <;> metta_call checked <;> ml_compare_eval [] unfolding [name, primitive, node, ordering]
  all_goals dsimp only [OCaml.comparison, BEq.beq, bne, Bool.not]
  all_goals
    apply result_at
    first
    | exact order_equal state _ _ .lt .eq (bound_returns _ _ _ (by rfl))
    | exact order_equal state _ _ .eq .eq (bound_returns _ _ _ (by rfl))
    | exact order_equal state _ _ .gt .eq (bound_returns _ _ _ (by rfl))
    | exact order_equal state _ _ .lt .lt (bound_returns _ _ _ (by rfl))
    | exact order_equal state _ _ .eq .lt (bound_returns _ _ _ (by rfl))
    | exact order_equal state _ _ .gt .lt (bound_returns _ _ _ (by rfl))
    | exact order_equal state _ _ .lt .gt (bound_returns _ _ _ (by rfl))
    | exact order_equal state _ _ .eq .gt (bound_returns _ _ _ (by rfl))
    | exact order_equal state _ _ .gt .gt (bound_returns _ _ _ (by rfl))
    | apply pure_if_returns
      · first
        | exact order_equal state _ _ .lt .eq (bound_returns _ _ _ (by rfl))
        | exact order_equal state _ _ .eq .eq (bound_returns _ _ _ (by rfl))
        | exact order_equal state _ _ .gt .eq (bound_returns _ _ _ (by rfl))
        | exact order_equal state _ _ .lt .gt (bound_returns _ _ _ (by rfl))
        | exact order_equal state _ _ .eq .gt (bound_returns _ _ _ (by rfl))
        | exact order_equal state _ _ .gt .gt (bound_returns _ _ _ (by rfl))
        | exact order_equal state _ _ .lt .lt (bound_returns _ _ _ (by rfl))
        | exact order_equal state _ _ .eq .lt (bound_returns _ _ _ (by rfl))
        | exact order_equal state _ _ .gt .lt (bound_returns _ _ _ (by rfl))
      · simp
        exact grounded_returns _ _ _ _

theorem functional_returns (state : State) (operator : String) :
    PureReturns runtime [] state
      (apply "gslt:ml:comparison" [encoded (.string operator), encoded (.symbol "MlFunctionalOrder")]) state
      (encoded (OCamlResultServices.faultResult "MlFunctionalComparison")) := by
  have fault := OCamlResultServices.fault_result_returns state "MlFunctionalComparison"
  metta_call checked
  ml_compare_eval [fault] unfolding []

theorem incomparable_returns (state : State) (operator : String) :
    PureReturns runtime [] state
      (apply "gslt:ml:comparison" [encoded (.string operator), encoded (.symbol "MlIncomparable")]) state (encoded (.symbol "None")) := by
  metta_call checked
  ml_compare_eval [] unfolding []

#print axioms operator_exact
#print axioms comparison_returns
#print axioms functional_returns
#print axioms incomparable_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonFormatter
