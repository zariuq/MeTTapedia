import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareTraversal
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonResult
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlValuesExecution

/-! The public primitive dispatcher realizes all six source comparison
operators using the actual linked arguments and shared structural service.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonPrimitive

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution OCamlComparisonFormatter

theorem returns (state : State) (operator : OCaml.Primitive) (allowed : operator.isComparison = true)
    (left right : OCaml.Value) :
    PureReturns runtime [] state (apply "gslt:ml:primitive"
      [encoded (InferenceCettaWire.encodePattern (primitive operator)), encoded (fieldsTerm [left, right])]) state
      (encoded (OCamlComparisonResult.sourceResult (operator.eval [left, right]))) := by
  have values := OCamlValuesExecution.values_returns state [left, right]
  have compared := OCamlCompareTraversal.value_returns state left right
  have formatted := OCamlComparisonResult.returns state operator allowed (OCaml.compareValue left right)
    (OCaml.comparison_outcome left right)
  rw [OCaml.comparison_evaluates operator allowed, operator_exact]
  cases operator <;> simp [OCaml.Primitive.isComparison] at allowed
  all_goals
    metta_call checked
    ml_compare_eval [values, compared, formatted] unfolding [name, primitive, node, OCamlValuesExecution.valuesTerm, encodeList]

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonPrimitive
