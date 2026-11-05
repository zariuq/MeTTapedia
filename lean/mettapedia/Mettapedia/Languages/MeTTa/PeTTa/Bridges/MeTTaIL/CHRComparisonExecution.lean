import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRControllerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScalarEqualityExecution
import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemandLibrary
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRExecutionData

/-! Ground CHR comparisons execute the literal controller source. Signed
integer inputs are retained exactly, and every comparison preserves the
complete target state. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRComparisonExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit CHRControllerSource

abbrev comparison := ModuleFormat.CHRCompilation.ExecutionData.comparison

private theorem greater_returns (state : State)
    (caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (left right : Atom) (first second : Int)
    (one : PureReturns runtime caller state left state (integer first))
    (two : PureReturns runtime caller state right state (integer second)) :
    PureReturns runtime caller state (apply ">" [left, right]) state
      (Effects.boolean (decide (second < first))) := by
  exact native_binary_call_returns runtime caller state state state state ">" _ _ _ _ _
    (by decide) (by decide) (by rw [native_raw runtime ">" 0 (by decide)]; decide)
    (by rw [native_raw runtime ">" 1 (by decide)]; decide) one two rfl (by decide)

theorem equal_body_returns (state : State) (left right : Int) :
    PureReturns runtime
      (Library.bind ["operator", "left", "right"]
        [encoded (comparison .equal), integer left, integer right]) state
      (library.body "gslt:chr:comparison") state
      (Effects.boolean (CHR.Comparison.holds .equal left right)) := by
  metta_literal
  metta_eval with checked unfolding [comparison, ModuleFormat.CHRCompilation.ExecutionData.comparison]
  have same : decide (left = right) = (left == right) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
  simpa only [CHR.Comparison.holds, same] using
    (integer_equal_returns runtime _ state _ _ left right
      (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl)))

theorem body_returns (state : State) (operator : CHR.Comparison) (left right : Int) :
    PureReturns runtime
      (Library.bind ["operator", "left", "right"]
        [encoded (comparison operator), integer left, integer right]) state
      (library.body "gslt:chr:comparison") state
      (Effects.boolean (operator.holds left right)) := by
  cases operator with
  | equal => exact equal_body_returns state left right
  | different =>
      metta_literal
      metta_eval with checked unfolding [comparison, ModuleFormat.CHRCompilation.ExecutionData.comparison]
      apply pure_if_returns
      · exact integer_equal_returns runtime _ state _ _ left right
          (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
      · by_cases same : left = right
        · subst right
          simp only [decide_true, if_true, CHR.Comparison.holds, bne_self_eq_false]
          exact grounded_returns _ _ _ _
        · have unequal : (left == right) = false := beq_eq_false_iff_ne.mpr same
          simp only [same, decide_false, Bool.false_eq_true, if_false, CHR.Comparison.holds, bne, unequal, Bool.not_false]
          exact grounded_returns _ _ _ _
  | less =>
      metta_literal
      metta_eval with checked unfolding [comparison, ModuleFormat.CHRCompilation.ExecutionData.comparison]
      exact integer_lt_returns runtime _ state _ _ left right
        (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
  | greater =>
      metta_literal
      metta_eval with checked unfolding [comparison, ModuleFormat.CHRCompilation.ExecutionData.comparison]
      exact greater_returns state _ _ _ left right
        (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
  | lessEqual =>
      metta_literal
      metta_eval with checked unfolding [comparison, ModuleFormat.CHRCompilation.ExecutionData.comparison]
      apply pure_if_returns
      · exact greater_returns state _ _ _ left right
          (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
      · by_cases less : right < left
        · have notLe : ¬ left ≤ right := by omega
          simp only [less, decide_true, if_true, CHR.Comparison.holds, notLe, decide_false]
          exact grounded_returns _ _ _ _
        · have le : left ≤ right := by omega
          simp only [less, decide_false, Bool.false_eq_true, if_false, CHR.Comparison.holds, le, decide_true]
          exact grounded_returns _ _ _ _
  | greaterEqual =>
      metta_literal
      metta_eval with checked unfolding [comparison, ModuleFormat.CHRCompilation.ExecutionData.comparison]
      apply pure_if_returns
      · exact integer_lt_returns runtime _ state _ _ left right
          (bound_returns _ _ _ (by rfl)) (bound_returns _ _ _ (by rfl))
      · by_cases less : left < right
        · have notGe : ¬ left ≥ right := by omega
          simp only [less, decide_true, if_true, CHR.Comparison.holds, notGe, decide_false]
          exact grounded_returns _ _ _ _
        · have ge : left ≥ right := by omega
          simp only [less, decide_false, Bool.false_eq_true, if_false, CHR.Comparison.holds, ge, decide_true]
          exact grounded_returns _ _ _ _

theorem returns (state : State) (operator : CHR.Comparison) (left right : Int) :
    PureReturns runtime [] state
      (apply "gslt:chr:comparison" [encoded (comparison operator), integer left, integer right]) state
      (Effects.boolean (operator.holds left right)) := by
  apply Library.demand_call checked (by rfl) (by decide +kernel) [] state state state
    [encoded (comparison operator), integer left, integer right]
    [encoded (comparison operator), integer left, integer right] _ (by metta_literal; rfl)
  · simpa only [CettaWireAtom.applySubst_encode, CHRControllerSource.runtime, WireKit.encoded] using
      (ArgumentsReturn.raw (program := runtime) (caller := []) (head := "gslt:chr:comparison") (index := 0)
        (argument := encoded (comparison operator)) (before := state) (after := state)
        (by decide +kernel)
        (.evaluated (by decide +kernel) (integer_returns runtime [] state left)
          (.evaluated (by decide +kernel) (integer_returns runtime [] state right) (.nil _ _))))
  · exact body_returns state operator left right

theorem negative_less_than_positive (state : State) :
    PureReturns runtime [] state
      (apply "gslt:chr:comparison" [encoded (comparison .less), integer (-7), integer 2]) state
      (Effects.boolean true) := returns state .less (-7) 2

theorem equal_is_not_different (state : State) (value : Int) :
    PureReturns runtime [] state
      (apply "gslt:chr:comparison" [encoded (comparison .different), integer value, integer value]) state
      (Effects.boolean false) := by
  simpa only [CHR.Comparison.holds, bne_self_eq_false] using returns state .different value value

#print axioms body_returns
#print axioms returns
#print axioms negative_less_than_positive
#print axioms equal_is_not_different

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRComparisonExecution
