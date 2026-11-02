import Mettapedia.Languages.OCaml.ExpressionAssemblyCorrectness

/-! Independent bounded decoding of instruction data back to expression
trees. Decoding never calls the assembler. A graph reading supplies enough
fuel and is unique; allocated code cannot describe another expression tree. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.ExpressionTree

mutual
  def readFuel (arena : Array Instruction) : Nat → Code → Option ExpressionTree
    | 0, _ => none
    | fuel + 1, code => do
      match ← arena[code]? with
      | .literal value => pure (.literal value)
      | .variable index => pure (.variableRef index)
      | .lambda pattern body => pure (.lambda pattern (← readFuel arena fuel body))
      | .apply function argument => pure (.apply (← readFuel arena fuel function) (← readFuel arena fuel argument))
      | .letValue pattern value body => pure (.letValue pattern (← readFuel arena fuel value) (← readFuel arena fuel body))
      | .letRecursive definitions body => pure (.letRecursive (← readFields arena fuel definitions) (← readFuel arena fuel body))
      | .branch condition yes no => pure (.branch (← readFuel arena fuel condition) (← readFuel arena fuel yes) (← readFuel arena fuel no))
      | .andThen left right => pure (.andThen (← readFuel arena fuel left) (← readFuel arena fuel right))
      | .orElse left right => pure (.orElse (← readFuel arena fuel left) (← readFuel arena fuel right))
      | .tuple fields => pure (.tuple (← readFields arena fuel fields))
      | .cons head tail => pure (.cons (← readFuel arena fuel head) (← readFuel arena fuel tail))
      | .variant typeId constructor fields => pure (.variant typeId constructor (← readFields arena fuel fields))
      | .matchValue scrutinee clauses => pure (.matchValue (← readFuel arena fuel scrutinee) (← readClauses arena fuel clauses))
      | .primitive operator arguments => pure (.primitive operator (← readFields arena fuel arguments))
    termination_by fuel => (fuel, 0)

  def readFields (arena : Array Instruction) (fuel : Nat) : List Code → Option (List ExpressionTree)
    | [] => some []
    | first :: rest => do pure ((← readFuel arena fuel first) :: (← readFields arena fuel rest))
    termination_by codes => (fuel, codes.length + 1)

  def readClauses (arena : Array Instruction) (fuel : Nat) : List Clause → Option (List (MatchPattern × ExpressionTree))
    | [] => some []
    | first :: rest => do pure ((first.pattern, ← readFuel arena fuel first.body) :: (← readClauses arena fuel rest))
    termination_by clauses => (fuel, clauses.length + 1)
end

mutual
  theorem readFuel_of_reads {arena : Array Instruction} {tree : ExpressionTree} {code : Code}
      (read : Reads arena tree code) (fuel : Nat) (enough : sizeOf tree < fuel) : readFuel arena fuel code = some tree := by
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases read with
      | literal row => simp [readFuel, row]
      | «variable» row => simp [readFuel, row]
      | lambda row child =>
        simp only [ExpressionTree.lambda.sizeOf_spec] at enough
        simp [readFuel, row, readFuel_of_reads child fuel (by omega)]
      | apply row first second =>
        simp only [ExpressionTree.apply.sizeOf_spec] at enough
        simp [readFuel, row, readFuel_of_reads first fuel (by omega), readFuel_of_reads second fuel (by omega)]
      | letValue row first second =>
        simp only [ExpressionTree.letValue.sizeOf_spec] at enough
        simp [readFuel, row, readFuel_of_reads first fuel (by omega), readFuel_of_reads second fuel (by omega)]
      | letRecursive row functions child =>
        simp only [ExpressionTree.letRecursive.sizeOf_spec] at enough
        simp [readFuel, row, readFields_of_reads functions fuel (by omega), readFuel_of_reads child fuel (by omega)]
      | branch row test yes no =>
        simp only [ExpressionTree.branch.sizeOf_spec] at enough
        simp [readFuel, row, readFuel_of_reads test fuel (by omega), readFuel_of_reads yes fuel (by omega),
          readFuel_of_reads no fuel (by omega)]
      | andThen row first second =>
        simp only [ExpressionTree.andThen.sizeOf_spec] at enough
        simp [readFuel, row, readFuel_of_reads first fuel (by omega), readFuel_of_reads second fuel (by omega)]
      | orElse row first second =>
        simp only [ExpressionTree.orElse.sizeOf_spec] at enough
        simp [readFuel, row, readFuel_of_reads first fuel (by omega), readFuel_of_reads second fuel (by omega)]
      | tuple row children =>
        simp only [ExpressionTree.tuple.sizeOf_spec] at enough
        simp [readFuel, row, readFields_of_reads children fuel (by omega)]
      | cons row first second =>
        simp only [ExpressionTree.cons.sizeOf_spec] at enough
        simp [readFuel, row, readFuel_of_reads first fuel (by omega), readFuel_of_reads second fuel (by omega)]
      | variant row children =>
        simp only [ExpressionTree.variant.sizeOf_spec] at enough
        simp [readFuel, row, readFields_of_reads children fuel (by omega)]
      | matchValue row child branches =>
        simp only [ExpressionTree.matchValue.sizeOf_spec] at enough
        simp [readFuel, row, readFuel_of_reads child fuel (by omega), readClauses_of_reads branches fuel (by omega)]
      | primitive row children =>
        simp only [ExpressionTree.primitive.sizeOf_spec] at enough
        simp [readFuel, row, readFields_of_reads children fuel (by omega)]
    termination_by sizeOf tree

  theorem readFields_of_reads {arena : Array Instruction} {trees : List ExpressionTree} {codes : List Code}
      (read : FieldsRead arena trees codes) (fuel : Nat) (enough : sizeOf trees < fuel) : readFields arena fuel codes = some trees := by
    cases read with
    | nil => simp [readFields]
    | cons head tail =>
      simp only [List.cons.sizeOf_spec] at enough
      simp [readFields, readFuel_of_reads head fuel (by omega), readFields_of_reads tail fuel (by omega)]
    termination_by sizeOf trees

  theorem readClauses_of_reads {arena : Array Instruction} {trees : List (MatchPattern × ExpressionTree)} {clauses : List Clause}
      (read : ClausesRead arena trees clauses) (fuel : Nat) (enough : sizeOf trees < fuel) : readClauses arena fuel clauses = some trees := by
    cases read with
    | nil => simp [readClauses]
    | cons head tail =>
      simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at enough
      simp [readClauses, readFuel_of_reads head fuel (by omega), readClauses_of_reads tail fuel (by omega)]
    termination_by sizeOf trees
end

theorem Reads.unique {arena : Array Instruction} {first second : ExpressionTree} {code : Code}
    (left : Reads arena first code) (right : Reads arena second code) : first = second := by
  have one := readFuel_of_reads left (sizeOf first + sizeOf second + 1) (by omega)
  have two := readFuel_of_reads right (sizeOf first + sizeOf second + 1) (by omega)
  exact Option.some.inj (one.symm.trans two)

theorem assembled_readback (tree : ExpressionTree) (constructors : List Constructor) :
    readFuel (tree.assemble constructors).code (sizeOf tree + 1) (tree.assemble constructors).entry = some tree :=
  readFuel_of_reads (assembled_reads tree constructors) _ (by omega)

#print axioms readFuel_of_reads
#print axioms readFields_of_reads
#print axioms readClauses_of_reads
#print axioms Reads.unique
#print axioms assembled_readback

end Mettapedia.Languages.OCaml.ExpressionTree
