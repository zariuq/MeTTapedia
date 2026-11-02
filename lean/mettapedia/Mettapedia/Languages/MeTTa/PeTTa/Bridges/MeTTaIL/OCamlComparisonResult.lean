import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonFormatter
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlArithmeticAdequacy
import Mettapedia.Languages.OCaml.ComparisonPrimitive

/-! The existing result formatter realizes the source comparison result
map. Only source refusals map to None; functional comparison remains a fault.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonResult

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlOrderExecution OCamlComparisonFormatter

def sourceResult (result : Except OCaml.InternalError OCaml.Result) : Term :=
  match result with
  | .error _ => .symbol "None"
  | .ok result => OCamlArithmeticAdequacy.resultTerm result

theorem supported_exact (operator : OCaml.Primitive) : supported operator = operator.isComparison := by
  cases operator <;> rfl

theorem returns (state : State) (operator : OCaml.Primitive) (allowed : operator.isComparison = true)
    (result : OCaml.Compared) (outcome : OCaml.ComparisonOutcome result) :
    PureReturns runtime [] state (apply "gslt:ml:comparison" [encoded (.string (name operator)), encoded (view result)]) state
      (encoded (sourceResult (OCaml.comparisonResult operator result))) := by
  cases outcome with
  | refused error => exact incomparable_returns state (name operator)
  | functional =>
    have actual := functional_returns state (name operator)
    have fault := OCamlResultServices.fault_result_exact OCaml.Fault.functionalComparison
    simp only [OCamlResultServices.faultName] at fault
    rw [fault] at actual
    exact actual
  | ordered order =>
    have actual := comparison_returns state operator (by rw [supported_exact]; exact allowed) order
    rw [OCamlResultServices.boolean_result_exact] at actual
    exact actual

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonResult
