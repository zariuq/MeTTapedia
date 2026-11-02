import Mettapedia.Languages.OCaml.TreeValueCorrespondence
import Mettapedia.Languages.OCaml.ExpressionDecoding

/-! A fixed indexed value has at most one related tree value. Physical code
addresses may differ between related implementations, but reading one fixed
address recovers a unique body, group and captured environment. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

mutual
  theorem TreeValueRelated.left_unique {arena : Array Instruction} {first second : TreeValue} {value : Value}
      (left : TreeValueRelated arena first value) (right : TreeValueRelated arena second value) : first = second :=
    match left with
    | .literal value => by cases right; rfl
    | .tuple fields => by
        cases right with
        | tuple other => exact congrArg TreeValue.tuple (fields.left_unique other)
    | .cons head tail => by
        cases right with
        | cons front back => exact congrArg₂ TreeValue.cons (head.left_unique front) (tail.left_unique back)
    | .variant fields => by
        cases right with
        | variant other => exact congrArg (TreeValue.variant _ _) (fields.left_unique other)
    | .lambda read captures => by
        cases right with
        | lambda other captured =>
            have same := read.unique other
            cases same
            exact congrArg (TreeValue.closure _) (captures.left_unique captured)
    | .recursive read captures => by
        cases right with
        | recursive other captured =>
            have same := read.unique other
            cases same
            exact congrArg (TreeValue.closure _) (captures.left_unique captured)
    termination_by structural left

  theorem TreeValuesRelated.left_unique {arena : Array Instruction} {first second : List TreeValue} {values : List Value}
      (left : TreeValuesRelated arena first values) (right : TreeValuesRelated arena second values) : first = second :=
    match left with
    | .nil => by cases right; rfl
    | .cons head tail => by
        cases right with
        | cons front back => exact congrArg₂ List.cons (head.left_unique front) (tail.left_unique back)
    termination_by structural left
end

theorem TreeResultRelated.left_unique {arena : Array Instruction} {first second : TreeResult} {value : Result}
    (left : TreeResultRelated arena first value) (right : TreeResultRelated arena second value) : first = second := by
  cases left with
  | fault error => cases right; rfl
  | value aligned => cases right with | value other => exact congrArg Except.ok (aligned.left_unique other)

end Mettapedia.Languages.OCaml
