import Mettapedia.Languages.OCaml.ExpressionGraph

/-! Code allocation is append-only. Constructor assembly transports earlier
tree readings through later allocations before installing the parent row. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.Assembly

open ExpressionTree

structure Extension (before after : Array Instruction) : Prop where
  size_le : before.size ≤ after.size
  kept : ∀ index, index < before.size → after[index]? = before[index]?

theorem Extension.refl (arena : Array Instruction) : Extension arena arena := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Extension.trans {first second third : Array Instruction}
    (one : Extension first second) (two : Extension second third) : Extension first third :=
  ⟨Nat.le_trans one.size_le two.size_le, fun index bounded =>
    (two.kept index (Nat.lt_of_lt_of_le bounded one.size_le)).trans (one.kept index bounded)⟩

theorem Extension.lookup {before after : Array Instruction} (extension : Extension before after)
    (index : Nat) (instruction : Instruction) (found : before[index]? = some instruction) :
    after[index]? = some instruction := by
  have bounded : index < before.size := (Array.getElem?_eq_some_iff.mp found).1
  rw [extension.kept index bounded, found]

theorem push_extension (arena : Array Instruction) (instruction : Instruction) : Extension arena (arena.push instruction) :=
  ⟨by simp, fun _ bounded => by simp only [Array.getElem?_push, if_neg (Nat.ne_of_lt bounded)]⟩

def Builds (tree : ExpressionTree) (builder : Expression) : Prop :=
  ∀ arena, let result := builder.run arena
    Extension arena result.2 ∧ Reads result.2 tree result.1

theorem builds_emit (tree : ExpressionTree) (instruction : Instruction)
    (introduce : ∀ arena code, arena[code]? = some instruction → Reads arena tree code) :
    Builds tree (emit instruction) := by
  intro arena
  exact ⟨push_extension arena instruction, introduce _ _ (emit_installed instruction arena)⟩

theorem builds_unary {child parent : ExpressionTree} {builder : Expression} (built : Builds child builder)
    (operation : Code → Instruction)
    (introduce : ∀ arena code childCode, arena[code]? = some (operation childCode) →
      Reads arena child childCode → Reads arena parent code) :
    Builds parent (do let code ← builder; emit (operation code)) := by
  intro arena
  have childBuilt := built arena
  let result := builder.run arena
  change Extension arena (result.2.push (operation result.1)) ∧
    Reads (result.2.push (operation result.1)) parent result.2.size
  exact ⟨childBuilt.1.trans (push_extension _ _), introduce _ _ _ (emit_installed _ _)
    (childBuilt.2.mono (push_extension _ _).lookup)⟩

theorem builds_binary {left right parent : ExpressionTree} {first second : Expression}
    (leftBuilt : Builds left first) (rightBuilt : Builds right second) (operation : Code → Code → Instruction)
    (introduce : ∀ arena code leftCode rightCode, arena[code]? = some (operation leftCode rightCode) →
      Reads arena left leftCode → Reads arena right rightCode → Reads arena parent code) :
    Builds parent (do let leftCode ← first; let rightCode ← second; emit (operation leftCode rightCode)) := by
  intro arena
  let one := first.run arena
  let two := second.run one.2
  have leftProof := leftBuilt arena
  have rightProof := rightBuilt one.2
  have extension := (rightProof.1.trans (push_extension _ (operation one.1 two.1)))
  change Extension arena (two.2.push (operation one.1 two.1)) ∧
    Reads (two.2.push (operation one.1 two.1)) parent two.2.size
  exact ⟨leftProof.1.trans extension, introduce _ _ _ _ (emit_installed _ _)
    (leftProof.2.mono extension.lookup) (rightProof.2.mono (push_extension _ _).lookup)⟩

theorem builds_ternary {firstTree secondTree thirdTree parent : ExpressionTree}
    {first second third : Expression} (firstBuilt : Builds firstTree first) (secondBuilt : Builds secondTree second)
    (thirdBuilt : Builds thirdTree third) (operation : Code → Code → Code → Instruction)
    (introduce : ∀ arena code firstCode secondCode thirdCode,
      arena[code]? = some (operation firstCode secondCode thirdCode) →
      Reads arena firstTree firstCode → Reads arena secondTree secondCode → Reads arena thirdTree thirdCode →
      Reads arena parent code) :
    Builds parent (do let a ← first; let b ← second; let c ← third; emit (operation a b c)) := by
  intro arena
  let one := first.run arena
  let two := second.run one.2
  let three := third.run two.2
  have oneProof := firstBuilt arena
  have twoProof := secondBuilt one.2
  have threeProof := thirdBuilt two.2
  have tail := threeProof.1.trans (push_extension _ (operation one.1 two.1 three.1))
  change Extension arena (three.2.push (operation one.1 two.1 three.1)) ∧
    Reads (three.2.push (operation one.1 two.1 three.1)) parent three.2.size
  exact ⟨oneProof.1.trans (twoProof.1.trans tail), introduce _ _ _ _ _ (emit_installed _ _)
    (oneProof.2.mono (twoProof.1.trans tail).lookup) (twoProof.2.mono tail.lookup)
    (threeProof.2.mono (push_extension _ _).lookup)⟩

def BuildsFields (trees : List ExpressionTree) (builders : List Expression) : Prop :=
  ∀ arena, let result := (builders.mapM id).run arena
    Extension arena result.2 ∧ FieldsRead result.2 trees result.1

theorem builds_fields_nil : BuildsFields [] [] := fun arena => ⟨Extension.refl arena, .nil⟩

theorem builds_fields_cons {tree : ExpressionTree} {trees : List ExpressionTree}
    {builder : Expression} {builders : List Expression} (headBuilt : Builds tree builder)
    (tailBuilt : BuildsFields trees builders) : BuildsFields (tree :: trees) (builder :: builders) := by
  intro arena
  let one := builder.run arena
  let two := (builders.mapM id).run one.2
  have first := headBuilt arena
  have rest := tailBuilt one.2
  simp only [List.mapM_cons]
  change Extension arena two.2 ∧ FieldsRead two.2 (tree :: trees) (one.1 :: two.1)
  exact ⟨first.1.trans rest.1, .cons (first.2.mono rest.1.lookup) rest.2⟩

theorem builds_fields_node {trees : List ExpressionTree} {builders : List Expression} (children : BuildsFields trees builders)
    (parent : ExpressionTree) (operation : List Code → Instruction)
    (introduce : ∀ arena code codes, arena[code]? = some (operation codes) → FieldsRead arena trees codes → Reads arena parent code) :
    Builds parent (do let codes ← builders.mapM id; emit (operation codes)) := by
  intro arena
  let result := (builders.mapM id).run arena
  have built := children arena
  change Extension arena (result.2.push (operation result.1)) ∧
    Reads (result.2.push (operation result.1)) parent result.2.size
  exact ⟨built.1.trans (push_extension _ _), introduce _ _ _ (emit_installed _ _)
    (built.2.mono (push_extension _ _).lookup)⟩

theorem builds_functions {trees : List ExpressionTree} {builders : List Expression} {body : ExpressionTree}
    {bodyBuilder : Expression} (functions : BuildsFields trees builders) (bodyBuilt : Builds body bodyBuilder) :
    Builds (.letRecursive trees body) (letRecursive builders bodyBuilder) := by
  intro arena
  let one := (builders.mapM id).run arena
  let two := bodyBuilder.run one.2
  have functionProof := functions arena
  have bodyProof := bodyBuilt one.2
  have extension := bodyProof.1.trans (push_extension _ (.letRecursive one.1 two.1))
  change Extension arena (two.2.push (.letRecursive one.1 two.1)) ∧
    Reads (two.2.push (.letRecursive one.1 two.1)) (.letRecursive trees body) two.2.size
  exact ⟨functionProof.1.trans extension, .letRecursive (emit_installed _ _)
    (functionProof.2.mono extension.lookup) (bodyProof.2.mono (push_extension _ _).lookup)⟩

def BuildsClauses (trees : List (MatchPattern × ExpressionTree)) (builders : List (MatchPattern × Expression)) : Prop :=
  ∀ arena, let result := (builders.mapM fun (clause : MatchPattern × Expression) => do pure (Clause.mk clause.1 (← clause.2))).run arena
    Extension arena result.2 ∧ ClausesRead result.2 trees result.1

theorem builds_clauses_nil : BuildsClauses [] [] := fun arena => ⟨Extension.refl arena, .nil⟩

theorem builds_clauses_cons {pattern : MatchPattern} {body : ExpressionTree} {trees : List (MatchPattern × ExpressionTree)}
    {builder : Expression} {builders : List (MatchPattern × Expression)}
    (bodyBuilt : Builds body builder) (restBuilt : BuildsClauses trees builders) :
    BuildsClauses ((pattern, body) :: trees) ((pattern, builder) :: builders) := by
  intro arena
  let one := builder.run arena
  let two := (builders.mapM fun (clause : MatchPattern × Expression) => do pure (Clause.mk clause.1 (← clause.2))).run one.2
  have first := bodyBuilt arena
  have rest := restBuilt one.2
  simp only [List.mapM_cons]
  change Extension arena two.2 ∧ ClausesRead two.2 ((pattern, body) :: trees) (⟨pattern, one.1⟩ :: two.1)
  exact ⟨first.1.trans rest.1, .cons (first.2.mono rest.1.lookup) rest.2⟩

theorem builds_match {scrutinee : ExpressionTree} {trees : List (MatchPattern × ExpressionTree)}
    {builder : Expression} {builders : List (MatchPattern × Expression)}
    (scrutineeBuilt : Builds scrutinee builder) (clausesBuilt : BuildsClauses trees builders) :
    Builds (.matchValue scrutinee trees) (matchValue builder builders) := by
  intro arena
  let one := builder.run arena
  let two := (builders.mapM fun (clause : MatchPattern × Expression) => do pure (Clause.mk clause.1 (← clause.2))).run one.2
  have first := scrutineeBuilt arena
  have rest := clausesBuilt one.2
  have extension := rest.1.trans (push_extension _ (.matchValue one.1 two.1))
  change Extension arena (two.2.push (.matchValue one.1 two.1)) ∧
    Reads (two.2.push (.matchValue one.1 two.1)) (.matchValue scrutinee trees) two.2.size
  exact ⟨first.1.trans extension, .matchValue (emit_installed _ _)
    (first.2.mono extension.lookup) (rest.2.mono (push_extension _ _).lookup)⟩

#print axioms Extension.lookup
#print axioms builds_emit
#print axioms builds_unary
#print axioms builds_binary
#print axioms builds_ternary
#print axioms builds_fields_cons
#print axioms builds_fields_node
#print axioms builds_functions
#print axioms builds_clauses_cons
#print axioms builds_match

end Mettapedia.Languages.OCaml.Assembly
