import Mettapedia.Languages.OCaml.TreeEvaluation
import Mettapedia.Languages.OCaml.TreeValueCorrespondence
import Mettapedia.Languages.OCaml.PrimitiveShape

/-! Arithmetic and comparison transfer between tree operands and allocated
values, including functional-comparison and division faults. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

theorem Primitive.eval_shape_ok (operator : Primitive) {first second : List Value} (same : FieldsShape first second)
    {result : Result} (calculated : operator.eval first = .ok result) : operator.eval second = .ok result := by
  have observed := operator.eval_shape same
  rw [calculated] at observed
  cases answer : operator.eval second with
  | error error => simp [answer, Except.toOption] at observed
  | ok actual =>
      have same : actual = result := Option.some.inj (by simpa only [answer, Except.toOption] using observed.symm)
      exact congrArg Except.ok same

theorem TreePrimitive.toIndexed {arena : Array Instruction} {operator : Primitive}
    {trees : List TreeValue} {values : List Value} (related : TreeValuesRelated arena trees values)
    {result : TreeResult} (calculated : TreePrimitive operator trees result) :
    ∃ actual, operator.eval values = .ok actual ∧ TreeResultRelated arena result actual := by
  cases calculated with
  | literal answer => exact ⟨_, operator.eval_shape_ok related.primitiveShapes answer, .value (.literal _)⟩
  | fault answer => exact ⟨_, operator.eval_shape_ok related.primitiveShapes answer, .fault _⟩

theorem TreePrimitive.fromIndexed {arena : Array Instruction} {operator : Primitive}
    {trees : List TreeValue} {values : List Value} (related : TreeValuesRelated arena trees values)
    {actual : Result} (calculated : operator.eval values = .ok actual) :
    ∃ result, TreePrimitive operator trees result ∧ TreeResultRelated arena result actual := by
  have source := operator.eval_shape_ok related.primitiveShapes.symm calculated
  obtain ⟨scalar, shape⟩ := operator.eval_scalar values calculated
  cases scalar with
  | error error =>
      subst actual
      exact ⟨.error error, .fault source, .fault error⟩
  | ok literal =>
      subst actual
      exact ⟨.ok (.literal literal), .literal source, .value (.literal literal)⟩

end Mettapedia.Languages.OCaml
