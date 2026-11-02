import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlIntegerResult

/-! Loaded Boolean and ordinary-fault result constructors use the same
source result tags as the compact OCaml IR.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlResultServices

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def booleanTerm (flag : Bool) : Term := .application "PApp" [.string (if flag then "MlTrue" else "MlFalse"), .symbol "LNil"]
def booleanResult (flag : Bool) : Term := .application "Some"
  [.application "PApp" [.string "MlPrimitiveValue", encodeList id [booleanTerm flag]]]
def faultName : OCaml.Fault → String
  | .divisionByZero => "MlDivisionByZero" | .matchFailure => "MlMatchFailure" | .functionalComparison => "MlFunctionalComparison"
def faultResult (name : String) : Term := .application "Some"
  [.application "PApp" [.string "MlPrimitiveFault", encodeList id [.application "PApp" [.string name, .symbol "LNil"]]]]

theorem boolean_body_returns (state : State) (flag : Bool) :
    PureReturns runtime (Library.bind ["value"] [Effects.boolean flag]) state
      (library.body "gslt:ml:boolean") state (encoded (booleanTerm flag)) := by
  metta_literal
  cases flag <;>
    (apply PureData.constructor_return runtime _ state "PApp" _ _ (by decide +kernel) (by decide)
     refine .cons ?_ (.cons (symbol_returns _ _ _ _) .nil)
     apply pure_if_returns
     · exact bound_returns _ _ _ (by rfl)
     · exact grounded_returns _ _ _ _)

theorem boolean_returns (state : State) (flag : Bool) :
    PureReturns runtime [] state (apply "gslt:ml:boolean" [Effects.boolean flag]) state (encoded (booleanTerm flag)) := by
  apply Library.demand_call checked (by rfl) (by decide +kernel) [] state state state
    [Effects.boolean flag] [Effects.boolean flag] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:boolean") (index := 0)
      (by decide +kernel) (grounded_returns _ _ _ _) (.nil _ _)
  · exact boolean_body_returns state flag

theorem boolean_result_body_returns (state : State) (flag : Bool) :
    PureReturns runtime (Library.bind ["boolean"] [Effects.boolean flag]) state
      (library.body "gslt:ml:result-boolean") state (encoded (booleanResult flag)) := by
  metta_literal
  apply pure_let_star_returns _ _ _ _ _ _ _ rfl
  apply pure_let_returns _ _ _ "value" _ (encoded (booleanTerm flag)) _ _ (by rfl)
  · apply Library.demand_call checked (head := "gslt:ml:boolean") (by rfl) (by decide +kernel)
      _ state state state _ [Effects.boolean flag] _ (by metta_literal; rfl)
    · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:boolean") (index := 0)
        (by decide +kernel) (bound_returns _ _ _ (by rfl)) (.nil _ _)
    · exact boolean_body_returns state flag
  · have pack := pack1_returns state "MlPrimitiveValue" (booleanTerm flag)
    metta_eval [pack] with checked unfolding [booleanResult]

theorem boolean_result_returns (state : State) (flag : Bool) :
    PureReturns runtime [] state (apply "gslt:ml:result-boolean" [Effects.boolean flag]) state (encoded (booleanResult flag)) := by
  apply Library.demand_call checked (by rfl) (by decide +kernel) [] state state state
    [Effects.boolean flag] [Effects.boolean flag] _ (by metta_literal; rfl)
  · exact ArgumentsReturn.evaluated (program := runtime) (head := "gslt:ml:result-boolean") (index := 0)
      (by decide +kernel) (grounded_returns _ _ _ _) (.nil _ _)
  · exact boolean_result_body_returns state flag

theorem fault_result_returns (state : State) (name : String) :
    PureReturns runtime [] state (apply "gslt:ml:result-fault" [encoded (.string name)]) state (encoded (faultResult name)) := by
  have pack := pack1_returns state "MlPrimitiveFault" (.application "PApp" [.string name, .symbol "LNil"])
  metta_call checked
  metta_eval [pack] with checked unfolding [faultResult]

theorem boolean_result_exact (flag : Bool) : booleanResult flag = .application "Some"
    [InferenceCettaWire.encodePattern (primitiveResult (.ok (.literal (.boolean flag))))] := by
  cases flag <;> simp only [booleanResult, booleanTerm, primitiveResult, value, literal, node,
    InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]

theorem fault_result_exact (error : OCaml.Fault) : faultResult (faultName error) = .application "Some"
    [InferenceCettaWire.encodePattern (primitiveResult (.error error))] := by
  cases error <;> simp only [faultResult, faultName, primitiveResult, fault, node,
    InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList, id_eq]

#print axioms boolean_returns
#print axioms boolean_result_returns
#print axioms fault_result_returns
#print axioms boolean_result_exact
#print axioms fault_result_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlResultServices
