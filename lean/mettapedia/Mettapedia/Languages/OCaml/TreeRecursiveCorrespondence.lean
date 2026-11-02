import Mettapedia.Languages.OCaml.TreeValueCorrespondence

/-! Recursive closures retain the group definition, slot and captured scope.
The source and target may allocate different physical child references. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

theorem ExpressionTree.FieldsRead.length {arena : Array Instruction} {trees : List ExpressionTree} {codes : List Code}
    (read : FieldsRead arena trees codes) : trees.length = codes.length := by
  induction trees generalizing codes with
  | nil => cases read; rfl
  | cons tree rest ih => cases read with | cons head tail => exact congrArg Nat.succ (ih tail)

theorem ExpressionTree.FieldsRead.getElem? {arena : Array Instruction} {trees : List ExpressionTree} {codes : List Code}
    (read : FieldsRead arena trees codes) (slot : Nat) {tree : ExpressionTree} (selected : trees[slot]? = some tree) :
    ∃ code, codes[slot]? = some code ∧ Reads arena tree code := by
  induction slot generalizing trees codes with
  | zero =>
      cases read with
      | nil => simp at selected
      | cons head tail => simp only [List.getElem?_cons_zero, Option.some.injEq] at selected; subst tree; exact ⟨_, rfl, head⟩
  | succ slot ih =>
      cases read with
      | nil => simp at selected
      | cons head tail => exact ih tail (by simpa using selected)

theorem ExpressionTree.FieldsRead.getElem?_back {arena : Array Instruction} {trees : List ExpressionTree} {codes : List Code}
    (read : FieldsRead arena trees codes) (slot : Nat) {code : Code} (selected : codes[slot]? = some code) :
    ∃ tree, trees[slot]? = some tree ∧ Reads arena tree code := by
  induction slot generalizing trees codes with
  | zero =>
      cases read with
      | nil => simp at selected
      | cons head tail => simp only [List.getElem?_cons_zero, Option.some.injEq] at selected; subst code; exact ⟨_, rfl, head⟩
  | succ slot ih =>
      cases read with
      | nil => simp at selected
      | cons head tail => exact ih tail (by simpa using selected)

theorem TreeValuesRelated.recursiveBindings {arena : Array Instruction} {definitions : List ExpressionTree}
    {body : ExpressionTree} {codes : List Code} {bodyCode group : Code}
    (row : arena[group]? = some (.letRecursive codes bodyCode))
    (functions : ExpressionTree.FieldsRead arena definitions codes) (child : ExpressionTree.Reads arena body bodyCode)
    {trees : TreeEnvironment} {values : Environment} (captures : TreeValuesRelated arena trees values) :
    TreeValuesRelated arena (recursiveTreeBindings definitions trees) (recursiveBindings group codes values) := by
  have read := ExpressionTree.Reads.letRecursive row functions child
  have slots (indices : List Nat) : TreeValuesRelated arena
      (indices.map fun slot => .closure (.recursive definitions slot) trees)
      (indices.map fun slot => .closure (.recursive group slot) values) := by
    induction indices with
    | nil => exact .nil
    | cons index rest ih => exact .cons (.recursive read captures) ih
  simpa only [recursiveTreeBindings, OCaml.recursiveBindings, functions.length] using slots (List.range codes.length)

theorem TreeValuesRelated.recursiveEnvironment {arena : Array Instruction} {definitions : List ExpressionTree}
    {body : ExpressionTree} {codes : List Code} {bodyCode group : Code}
    (row : arena[group]? = some (.letRecursive codes bodyCode))
    (functions : ExpressionTree.FieldsRead arena definitions codes) (child : ExpressionTree.Reads arena body bodyCode)
    {trees : TreeEnvironment} {values : Environment} (captures : TreeValuesRelated arena trees values) :
    TreeValuesRelated arena (recursiveTreeEnvironment definitions trees) (recursiveEnvironment group codes values) :=
  captures.extend (captures.recursiveBindings row functions child)

end Mettapedia.Languages.OCaml
