import Mettapedia.Languages.OCaml.ExpressionGraph
import Aesop

/-! Instruction lookup determines a tree node's constructor and child readings.
The result follows from the independent graph relation, not the assembler. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.ExpressionTree

theorem Reads.view_literal {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (value : Literal) (row : arena[code]? = some (.literal value)) :
    tree = .literal value := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.literal.injEq, reduceCtorEq]

theorem Reads.view_variable {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (index : Nat) (row : arena[code]? = some (.variable index)) :
    tree = .variableRef index := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.variable.injEq, reduceCtorEq]

theorem Reads.view_lambda {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (parameter : MatchPattern) (bodyCode : Code) (row : arena[code]? = some (.lambda parameter bodyCode)) :
    ∃ body, tree = .lambda parameter body ∧ Reads arena body bodyCode := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.lambda.injEq, reduceCtorEq]; aesop

theorem Reads.view_apply {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (functionCode argumentCode : Code) (row : arena[code]? = some (.apply functionCode argumentCode)) :
    ∃ function argument, tree = .apply function argument ∧ Reads arena function functionCode ∧ Reads arena argument argumentCode := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.apply.injEq, reduceCtorEq]; aesop

theorem Reads.view_letValue {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (parameter : MatchPattern) (valueCode bodyCode : Code) (row : arena[code]? = some (.letValue parameter valueCode bodyCode)) :
    ∃ value body, tree = .letValue parameter value body ∧ Reads arena value valueCode ∧ Reads arena body bodyCode := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.letValue.injEq, reduceCtorEq]; aesop

theorem Reads.view_letRecursive {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (codes : List Code) (bodyCode : Code) (row : arena[code]? = some (.letRecursive codes bodyCode)) :
    ∃ definitions body, tree = .letRecursive definitions body ∧ FieldsRead arena definitions codes ∧ Reads arena body bodyCode := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.letRecursive.injEq, reduceCtorEq]; aesop

theorem Reads.view_branch {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (conditionCode yesCode noCode : Code) (row : arena[code]? = some (.branch conditionCode yesCode noCode)) :
    ∃ condition yes no, tree = .branch condition yes no ∧ Reads arena condition conditionCode ∧ Reads arena yes yesCode ∧ Reads arena no noCode := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.branch.injEq, reduceCtorEq]; aesop

theorem Reads.view_andThen {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (leftCode rightCode : Code) (row : arena[code]? = some (.andThen leftCode rightCode)) :
    ∃ left right, tree = .andThen left right ∧ Reads arena left leftCode ∧ Reads arena right rightCode := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.andThen.injEq, reduceCtorEq]; aesop

theorem Reads.view_orElse {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (leftCode rightCode : Code) (row : arena[code]? = some (.orElse leftCode rightCode)) :
    ∃ left right, tree = .orElse left right ∧ Reads arena left leftCode ∧ Reads arena right rightCode := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.orElse.injEq, reduceCtorEq]; aesop

theorem Reads.view_tuple {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (codes : List Code) (row : arena[code]? = some (.tuple codes)) :
    ∃ fields, tree = .tuple fields ∧ FieldsRead arena fields codes := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.tuple.injEq, reduceCtorEq]; aesop

theorem Reads.view_cons {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (headCode tailCode : Code) (row : arena[code]? = some (.cons headCode tailCode)) :
    ∃ head tail, tree = .cons head tail ∧ Reads arena head headCode ∧ Reads arena tail tailCode := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.cons.injEq, reduceCtorEq]; aesop

theorem Reads.view_variant {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (typeId constructor : Nat) (codes : List Code) (row : arena[code]? = some (.variant typeId constructor codes)) :
    ∃ fields, tree = .variant typeId constructor fields ∧ FieldsRead arena fields codes := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.variant.injEq, reduceCtorEq]; aesop

theorem Reads.view_matchValue {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (scrutineeCode : Code) (clauses : List Clause) (row : arena[code]? = some (.matchValue scrutineeCode clauses)) :
    ∃ scrutinee branches, tree = .matchValue scrutinee branches ∧ Reads arena scrutinee scrutineeCode ∧ ClausesRead arena branches clauses := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.matchValue.injEq, reduceCtorEq]; aesop

theorem Reads.view_primitive {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
    (read : Reads arena tree code) (operator : Primitive) (codes : List Code) (row : arena[code]? = some (.primitive operator codes)) :
    ∃ arguments, tree = .primitive operator arguments ∧ FieldsRead arena arguments codes := by
  cases read <;> simp_all only [Option.some.injEq, Instruction.primitive.injEq, reduceCtorEq]; aesop

end Mettapedia.Languages.OCaml.ExpressionTree
