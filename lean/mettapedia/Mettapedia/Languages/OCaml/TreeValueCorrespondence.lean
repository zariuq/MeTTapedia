import Mettapedia.Languages.OCaml.TreeValue
import Mettapedia.Languages.OCaml.ExpressionGraph
import Mettapedia.Languages.OCaml.ValueShape

/-! Relating unallocated tree values to indexed values. Function closures
carry an independent instruction-graph reading and related captures; their
addresses are never inferred from a primitive operand view. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

mutual
  inductive TreeValueRelated (arena : Array Instruction) : TreeValue → Value → Prop where
    | literal (value : Literal) : TreeValueRelated arena (.literal value) (.literal value)
    | tuple {trees values} (fields : TreeValuesRelated arena trees values) :
        TreeValueRelated arena (.tuple trees) (.tuple values)
    | cons {head first tail rest} (front : TreeValueRelated arena head first)
        (back : TreeValueRelated arena tail rest) : TreeValueRelated arena (.cons head tail) (.cons first rest)
    | variant {typeId constructor trees values} (fields : TreeValuesRelated arena trees values) :
        TreeValueRelated arena (.variant typeId constructor trees) (.variant typeId constructor values)
    | lambda {parameter body code captured environment}
        (read : ExpressionTree.Reads arena (.lambda parameter body) code)
        (captures : TreeValuesRelated arena captured environment) :
        TreeValueRelated arena (.closure (.lambda parameter body) captured) (.closure (.lambda code) environment)
    | recursive {definitions body group slot captured environment}
        (read : ExpressionTree.Reads arena (.letRecursive definitions body) group)
        (captures : TreeValuesRelated arena captured environment) :
        TreeValueRelated arena (.closure (.recursive definitions slot) captured) (.closure (.recursive group slot) environment)

  inductive TreeValuesRelated (arena : Array Instruction) : List TreeValue → List Value → Prop where
    | nil : TreeValuesRelated arena [] []
    | cons {tree value trees values} (head : TreeValueRelated arena tree value)
        (tail : TreeValuesRelated arena trees values) : TreeValuesRelated arena (tree :: trees) (value :: values)
end

inductive TreeResultRelated (arena : Array Instruction) : TreeResult → Result → Prop where
  | value {tree value} (related : TreeValueRelated arena tree value) : TreeResultRelated arena (.ok tree) (.ok value)
  | fault (error : Fault) : TreeResultRelated arena (.error error) (.error error)

inductive TreeArgumentsRelated (arena : Array Instruction) : Except Fault (List TreeValue) → Except Fault (List Value) → Prop where
  | values {trees values} (related : TreeValuesRelated arena trees values) : TreeArgumentsRelated arena (.ok trees) (.ok values)
  | fault (error : Fault) : TreeArgumentsRelated arena (.error error) (.error error)

theorem TreeResultRelated.valueWitness {arena : Array Instruction} {tree : TreeValue} {P : Result → Prop}
    (found : ∃ actual, P actual ∧ TreeResultRelated arena (.ok tree) actual) :
    ∃ value, P (.ok value) ∧ TreeValueRelated arena tree value := by
  obtain ⟨actual, proof, related⟩ := found
  cases related with | value aligned => exact ⟨_, proof, aligned⟩

theorem TreeResultRelated.literalWitness {arena : Array Instruction} {literal : Literal} {P : Result → Prop}
    (found : ∃ actual, P actual ∧ TreeResultRelated arena (.ok (.literal literal)) actual) : P (.ok (.literal literal)) := by
  obtain ⟨actual, proof, related⟩ := TreeResultRelated.valueWitness found
  cases related
  exact proof

theorem TreeResultRelated.faultWitness {arena : Array Instruction} {error : Fault} {P : Result → Prop}
    (found : ∃ actual, P actual ∧ TreeResultRelated arena (.error error) actual) : P (.error error) := by
  obtain ⟨actual, proof, related⟩ := found
  cases related
  exact proof

theorem TreeArgumentsRelated.valuesWitness {arena : Array Instruction} {trees : List TreeValue}
    {P : Except Fault (List Value) → Prop}
    (found : ∃ actual, P actual ∧ TreeArgumentsRelated arena (.ok trees) actual) :
    ∃ values, P (.ok values) ∧ TreeValuesRelated arena trees values := by
  obtain ⟨actual, proof, related⟩ := found
  cases related with | values aligned => exact ⟨_, proof, aligned⟩

theorem TreeArgumentsRelated.faultWitness {arena : Array Instruction} {error : Fault}
    {P : Except Fault (List Value) → Prop}
    (found : ∃ actual, P actual ∧ TreeArgumentsRelated arena (.error error) actual) : P (.error error) := by
  obtain ⟨actual, proof, related⟩ := found
  cases related
  exact proof

theorem TreeResultRelated.valueWitness_back {arena : Array Instruction} {value : Value} {P : TreeResult → Prop}
    (found : ∃ tree, P tree ∧ TreeResultRelated arena tree (.ok value)) :
    ∃ tree, P (.ok tree) ∧ TreeValueRelated arena tree value := by
  obtain ⟨actual, proof, related⟩ := found
  cases related with | value aligned => exact ⟨_, proof, aligned⟩

theorem TreeResultRelated.literalWitness_back {arena : Array Instruction} {literal : Literal} {P : TreeResult → Prop}
    (found : ∃ tree, P tree ∧ TreeResultRelated arena tree (.ok (.literal literal))) : P (.ok (.literal literal)) := by
  obtain ⟨actual, proof, related⟩ := TreeResultRelated.valueWitness_back found
  cases related
  exact proof

theorem TreeResultRelated.faultWitness_back {arena : Array Instruction} {error : Fault} {P : TreeResult → Prop}
    (found : ∃ tree, P tree ∧ TreeResultRelated arena tree (.error error)) : P (.error error) := by
  obtain ⟨actual, proof, related⟩ := found
  cases related
  exact proof

theorem TreeArgumentsRelated.valuesWitness_back {arena : Array Instruction} {values : List Value}
    {P : Except Fault (List TreeValue) → Prop}
    (found : ∃ trees, P trees ∧ TreeArgumentsRelated arena trees (.ok values)) :
    ∃ trees, P (.ok trees) ∧ TreeValuesRelated arena trees values := by
  obtain ⟨actual, proof, related⟩ := found
  cases related with | values aligned => exact ⟨_, proof, aligned⟩

theorem TreeArgumentsRelated.faultWitness_back {arena : Array Instruction} {error : Fault}
    {P : Except Fault (List TreeValue) → Prop}
    (found : ∃ trees, P trees ∧ TreeArgumentsRelated arena trees (.error error)) : P (.error error) := by
  obtain ⟨actual, proof, related⟩ := found
  cases related
  exact proof

theorem TreeValuesRelated.length {arena : Array Instruction} {trees : List TreeValue} {values : List Value}
    (related : TreeValuesRelated arena trees values) : trees.length = values.length :=
  match related with
  | .nil => rfl
  | .cons _ tail => congrArg Nat.succ tail.length
termination_by structural related

theorem TreeValuesRelated.append {arena : Array Instruction} {trees more : List TreeValue} {values rest : List Value}
    (front : TreeValuesRelated arena trees values) (back : TreeValuesRelated arena more rest) :
    TreeValuesRelated arena (trees ++ more) (values ++ rest) :=
  match front with
  | .nil => back
  | .cons head tail => .cons head (tail.append back)
termination_by structural front

theorem TreeValuesRelated.reverse {arena : Array Instruction} {trees : List TreeValue} {values : List Value}
    (related : TreeValuesRelated arena trees values) : TreeValuesRelated arena trees.reverse values.reverse :=
  match related with
  | .nil => .nil
  | .cons head tail => by
      simpa only [List.reverse_cons] using tail.reverse.append (.cons head .nil)
termination_by structural related

theorem TreeValuesRelated.extend {arena : Array Instruction} {trees more : List TreeValue} {values rest : List Value}
    (environment : TreeValuesRelated arena trees values) (bindings : TreeValuesRelated arena more rest) :
    TreeValuesRelated arena (extendTree trees more) (extend values rest) :=
  bindings.reverse.append environment

theorem TreeValuesRelated.getElem? {arena : Array Instruction} {trees : List TreeValue} {values : List Value}
    (related : TreeValuesRelated arena trees values) (index : Nat) {tree : TreeValue} (found : trees[index]? = some tree) :
    ∃ value, values[index]? = some value ∧ TreeValueRelated arena tree value := by
  induction index generalizing trees values with
  | zero =>
      cases related with
      | nil => simp at found
      | cons head tail => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst tree; exact ⟨_, rfl, head⟩
  | succ index ih =>
      cases related with
      | nil => simp at found
      | cons head tail => exact ih tail (by simpa using found)

theorem TreeValuesRelated.getElem?_back {arena : Array Instruction} {trees : List TreeValue} {values : List Value}
    (related : TreeValuesRelated arena trees values) (index : Nat) {value : Value} (found : values[index]? = some value) :
    ∃ tree, trees[index]? = some tree ∧ TreeValueRelated arena tree value := by
  induction index generalizing trees values with
  | zero =>
      cases related with
      | nil => simp at found
      | cons head tail => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; exact ⟨_, rfl, head⟩
  | succ index ih =>
      cases related with
      | nil => simp at found
      | cons head tail => exact ih tail (by simpa using found)

mutual
  theorem TreeValueRelated.primitiveShape {arena : Array Instruction} {tree : TreeValue} {value : Value}
      (related : TreeValueRelated arena tree value) : ValueShape tree.primitiveOperand value :=
    match related with
    | .literal value => by simpa only [TreeValue.primitiveOperand] using ValueShape.literal value
    | .tuple fields => by simpa only [TreeValue.primitiveOperand] using ValueShape.tuple fields.primitiveShapes
    | .cons head tail => by simpa only [TreeValue.primitiveOperand] using ValueShape.cons head.primitiveShape tail.primitiveShape
    | .variant fields => by simpa only [TreeValue.primitiveOperand] using ValueShape.variant fields.primitiveShapes
    | .lambda _ _ => by simp only [TreeValue.primitiveOperand]; exact .closure _ _ _ _
    | .recursive _ _ => by simp only [TreeValue.primitiveOperand]; exact .closure _ _ _ _
    termination_by structural related

  theorem TreeValuesRelated.primitiveShapes {arena : Array Instruction} {trees : List TreeValue} {values : List Value}
      (related : TreeValuesRelated arena trees values) : FieldsShape (trees.map TreeValue.primitiveOperand) values :=
    match related with
    | .nil => .nil
    | .cons head tail => .cons head.primitiveShape tail.primitiveShapes
    termination_by structural related
end

end Mettapedia.Languages.OCaml
