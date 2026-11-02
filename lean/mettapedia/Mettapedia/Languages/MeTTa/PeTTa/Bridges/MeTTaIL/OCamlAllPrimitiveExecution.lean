import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveReflection
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlDivisionPrimitive
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlUnaryPrimitives
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlComparisonPrimitive
import Mettapedia.Languages.OCaml.PrimitiveArguments

/-! Every successful independent source primitive evaluation is realized by
the actual loaded public primitive dispatcher. The argument shape and the
result codec are derived; no loaded-computation witness is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAllPrimitiveExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource

theorem returns (state : State) (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (evaluated : operator.eval arguments = .ok result) :
    PureReturns runtime [] state (OCamlPrimitiveReflection.call operator arguments) state
      (encoded (OCamlArithmeticAdequacy.resultTerm result)) := by
  cases operator with
  | add =>
    obtain ⟨left, right, rfl⟩ := OCaml.integer_binary_arguments (operator := .add) (by simp) evaluated
    have actual := OCamlArithmeticSource.source_evaluates .add left right
    have same := Except.ok.inj (evaluated.symm.trans actual)
    subst result
    have computed := OCamlArithmeticPrimitive.primitive_returns state .add left right
    rw [OCamlIntegerResult.result_exact] at computed
    exact computed
  | subtract =>
    obtain ⟨left, right, rfl⟩ := OCaml.integer_binary_arguments (operator := .subtract) (by simp) evaluated
    have actual := OCamlArithmeticSource.source_evaluates .subtract left right
    have same := Except.ok.inj (evaluated.symm.trans actual)
    subst result
    have computed := OCamlArithmeticPrimitive.primitive_returns state .subtract left right
    rw [OCamlIntegerResult.result_exact] at computed
    exact computed
  | multiply =>
    obtain ⟨left, right, rfl⟩ := OCaml.integer_binary_arguments (operator := .multiply) (by simp) evaluated
    have actual := OCamlArithmeticSource.source_evaluates .multiply left right
    have same := Except.ok.inj (evaluated.symm.trans actual)
    subst result
    have computed := OCamlArithmeticPrimitive.primitive_returns state .multiply left right
    rw [OCamlIntegerResult.result_exact] at computed
    exact computed
  | divide =>
    obtain ⟨left, right, rfl⟩ := OCaml.integer_binary_arguments (operator := .divide) (by simp) evaluated
    have actual := OCamlDivisionSource.source_evaluates false left right
    have same := Except.ok.inj (evaluated.symm.trans actual)
    subst result
    have computed := OCamlDivisionPrimitive.primitive_returns state false left right
    rw [OCamlDivisionSource.result_exact] at computed
    exact computed
  | modulo =>
    obtain ⟨left, right, rfl⟩ := OCaml.integer_binary_arguments (operator := .modulo) (by simp) evaluated
    have actual := OCamlDivisionSource.source_evaluates true left right
    have same := Except.ok.inj (evaluated.symm.trans actual)
    subst result
    have computed := OCamlDivisionPrimitive.primitive_returns state true left right
    rw [OCamlDivisionSource.result_exact] at computed
    exact computed
  | negate =>
    obtain ⟨number, rfl⟩ := OCaml.negate_arguments evaluated
    have same : result = .ok (.literal (.integer (OCaml.wrapInteger (-number)))) := Except.ok.inj evaluated.symm
    subst result
    have computed := OCamlUnaryPrimitives.negate_returns state number
    rw [OCamlIntegerResult.result_exact] at computed
    exact computed
  | notBool =>
    obtain ⟨flag, rfl⟩ := OCaml.not_arguments evaluated
    have same : result = .ok (.literal (.boolean (!flag))) := Except.ok.inj evaluated.symm
    subst result
    have computed := OCamlUnaryPrimitives.not_returns state flag
    rw [OCamlResultServices.boolean_result_exact] at computed
    exact computed
  | equal =>
    obtain ⟨left, right, rfl⟩ := OCaml.comparison_arguments (operator := .equal) rfl evaluated
    have computed := OCamlComparisonPrimitive.returns state .equal rfl left right
    rw [evaluated] at computed
    exact computed
  | different =>
    obtain ⟨left, right, rfl⟩ := OCaml.comparison_arguments (operator := .different) rfl evaluated
    have computed := OCamlComparisonPrimitive.returns state .different rfl left right
    rw [evaluated] at computed
    exact computed
  | less =>
    obtain ⟨left, right, rfl⟩ := OCaml.comparison_arguments (operator := .less) rfl evaluated
    have computed := OCamlComparisonPrimitive.returns state .less rfl left right
    rw [evaluated] at computed
    exact computed
  | lessEqual =>
    obtain ⟨left, right, rfl⟩ := OCaml.comparison_arguments (operator := .lessEqual) rfl evaluated
    have computed := OCamlComparisonPrimitive.returns state .lessEqual rfl left right
    rw [evaluated] at computed
    exact computed
  | greater =>
    obtain ⟨left, right, rfl⟩ := OCaml.comparison_arguments (operator := .greater) rfl evaluated
    have computed := OCamlComparisonPrimitive.returns state .greater rfl left right
    rw [evaluated] at computed
    exact computed
  | greaterEqual =>
    obtain ⟨left, right, rfl⟩ := OCaml.comparison_arguments (operator := .greaterEqual) rfl evaluated
    have computed := OCamlComparisonPrimitive.returns state .greaterEqual rfl left right
    rw [evaluated] at computed
    exact computed

theorem result_iff (state : State) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (expected observed : OCaml.Result) (evaluated : operator.eval arguments = .ok expected) :
    Runs runtime {state := state, control := .evaluate [] (OCamlPrimitiveReflection.call operator arguments)}
      (.complete state [encoded (OCamlArithmeticAdequacy.resultTerm observed)] [] []) ↔
      operator.eval arguments = .ok observed :=
  OCamlPrimitiveReflection.result_iff state operator arguments expected observed evaluated
    (returns state operator arguments expected evaluated)

#print axioms returns
#print axioms result_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAllPrimitiveExecution
