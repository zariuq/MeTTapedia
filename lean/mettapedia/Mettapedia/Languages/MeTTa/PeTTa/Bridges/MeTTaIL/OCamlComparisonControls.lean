import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonAdequacy
import Mettapedia.Languages.OCaml.ComparisonControls

/-! Completed native observations distinguish strict-prefix success,
functional faults and refusals. No malformed comparison is a Boolean answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonControls

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

private def integer (number : Int) : OCaml.Value := .literal (.integer number)
private def closure : OCaml.Value := .closure (.lambda 0) []

theorem strict_prefix_value (state : State) :
    Runs runtime {state := state, control := .evaluate [] (OCamlPrimitiveReflection.call .less
      [.tuple [integer 0, closure], .tuple [integer 1, closure]])}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm (.ok (.literal (.boolean true))))] [] []) := by
  exact (OCamlComparisonAdequacy.result_iff state .less rfl _ _ _ _
    OCaml.ComparisonControls.strict_prefix_skips_function).mpr OCaml.ComparisonControls.strict_prefix_skips_function

theorem equal_prefix_fault (state : State) :
    Runs runtime {state := state, control := .evaluate [] (OCamlPrimitiveReflection.call .equal
      [.tuple [integer 0, closure], .tuple [integer 0, closure]])}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm (.error .functionalComparison))] [] []) := by
  exact (OCamlComparisonAdequacy.result_iff state .equal rfl _ _ _ _
    OCaml.ComparisonControls.equal_prefix_reaches_function).mpr OCaml.ComparisonControls.equal_prefix_reaches_function

theorem equal_prefix_no_boolean (state : State) (flag : Bool) :
    ¬ Runs runtime {state := state, control := .evaluate [] (OCamlPrimitiveReflection.call .equal
      [.tuple [integer 0, closure], .tuple [integer 0, closure]])}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm (.ok (.literal (.boolean flag))))] [] []) := by
  intro completed
  have impossible := (OCamlComparisonAdequacy.result_iff state .equal rfl _ _ _ _
    OCaml.ComparisonControls.equal_prefix_reaches_function).mp completed
  exact OCaml.ComparisonControls.equal_prefix_no_boolean flag impossible

#print axioms strict_prefix_value
#print axioms equal_prefix_fault
#print axioms equal_prefix_no_boolean

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonControls
