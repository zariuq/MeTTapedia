import Mettapedia.Languages.OCaml.ExpressionTree

/-! A tree's meaning as indexed instructions is stated independently of
the assembler. Every child occurrence retains its own reference and order;
equal subtrees need not share a physical code position. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.ExpressionTree

mutual
  inductive Reads (arena : Array Instruction) : ExpressionTree → Code → Prop where
    | literal {value code} (row : arena[code]? = some (.literal value)) : Reads arena (.literal value) code
    | variable {index code} (row : arena[code]? = some (.variable index)) : Reads arena (.variableRef index) code
    | lambda {pattern body bodyCode code} (row : arena[code]? = some (.lambda pattern bodyCode))
        (child : Reads arena body bodyCode) : Reads arena (.lambda pattern body) code
    | apply {function argument functionCode argumentCode code}
        (row : arena[code]? = some (.apply functionCode argumentCode))
        (first : Reads arena function functionCode) (second : Reads arena argument argumentCode) :
        Reads arena (.apply function argument) code
    | letValue {pattern value body valueCode bodyCode code}
        (row : arena[code]? = some (.letValue pattern valueCode bodyCode))
        (first : Reads arena value valueCode) (second : Reads arena body bodyCode) :
        Reads arena (.letValue pattern value body) code
    | letRecursive {definitions body definitionCodes bodyCode code}
        (row : arena[code]? = some (.letRecursive definitionCodes bodyCode))
        (functions : FieldsRead arena definitions definitionCodes) (child : Reads arena body bodyCode) :
        Reads arena (.letRecursive definitions body) code
    | branch {condition yes no conditionCode yesCode noCode code}
        (row : arena[code]? = some (.branch conditionCode yesCode noCode))
        (test : Reads arena condition conditionCode) (positive : Reads arena yes yesCode)
        (negative : Reads arena no noCode) : Reads arena (.branch condition yes no) code
    | andThen {left right leftCode rightCode code} (row : arena[code]? = some (.andThen leftCode rightCode))
        (first : Reads arena left leftCode) (second : Reads arena right rightCode) : Reads arena (.andThen left right) code
    | orElse {left right leftCode rightCode code} (row : arena[code]? = some (.orElse leftCode rightCode))
        (first : Reads arena left leftCode) (second : Reads arena right rightCode) : Reads arena (.orElse left right) code
    | tuple {fields codes code} (row : arena[code]? = some (.tuple codes))
        (children : FieldsRead arena fields codes) : Reads arena (.tuple fields) code
    | cons {head tail headCode tailCode code} (row : arena[code]? = some (.cons headCode tailCode))
        (first : Reads arena head headCode) (second : Reads arena tail tailCode) : Reads arena (.cons head tail) code
    | variant {typeId constructor fields codes code} (row : arena[code]? = some (.variant typeId constructor codes))
        (children : FieldsRead arena fields codes) : Reads arena (.variant typeId constructor fields) code
    | matchValue {scrutinee clauses scrutineeCode codeClauses code}
        (row : arena[code]? = some (.matchValue scrutineeCode codeClauses))
        (child : Reads arena scrutinee scrutineeCode) (branches : ClausesRead arena clauses codeClauses) :
        Reads arena (.matchValue scrutinee clauses) code
    | primitive {operator arguments codes code} (row : arena[code]? = some (.primitive operator codes))
        (children : FieldsRead arena arguments codes) : Reads arena (.primitive operator arguments) code

  inductive FieldsRead (arena : Array Instruction) : List ExpressionTree → List Code → Prop where
    | nil : FieldsRead arena [] []
    | cons {first rest code codes} (head : Reads arena first code) (tail : FieldsRead arena rest codes) :
        FieldsRead arena (first :: rest) (code :: codes)

  inductive ClausesRead (arena : Array Instruction) : List (MatchPattern × ExpressionTree) → List Clause → Prop where
    | nil : ClausesRead arena [] []
    | cons {pattern body rest code clauses} (head : Reads arena body code) (tail : ClausesRead arena rest clauses) :
        ClausesRead arena ((pattern, body) :: rest) (⟨pattern, code⟩ :: clauses)
end

mutual
  theorem Reads.mono {before after : Array Instruction}
      (kept : ∀ (reference : Nat) (instruction : Instruction), before[reference]? = some instruction → after[reference]? = some instruction)
      {tree : ExpressionTree} {code : Code} (read : Reads before tree code) : Reads after tree code :=
    match read with
    | .literal row => .literal (kept _ _ row)
    | .variable row => .variable (kept _ _ row)
    | .lambda row child => .lambda (kept _ _ row) (child.mono kept)
    | .apply row first second => .apply (kept _ _ row) (first.mono kept) (second.mono kept)
    | .letValue row first second => .letValue (kept _ _ row) (first.mono kept) (second.mono kept)
    | .letRecursive row functions child => .letRecursive (kept _ _ row) (functions.mono kept) (child.mono kept)
    | .branch row test yes no => .branch (kept _ _ row) (test.mono kept) (yes.mono kept) (no.mono kept)
    | .andThen row first second => .andThen (kept _ _ row) (first.mono kept) (second.mono kept)
    | .orElse row first second => .orElse (kept _ _ row) (first.mono kept) (second.mono kept)
    | .tuple row children => .tuple (kept _ _ row) (children.mono kept)
    | .cons row first second => .cons (kept _ _ row) (first.mono kept) (second.mono kept)
    | .variant row children => .variant (kept _ _ row) (children.mono kept)
    | .matchValue row child branches => .matchValue (kept _ _ row) (child.mono kept) (branches.mono kept)
    | .primitive row children => .primitive (kept _ _ row) (children.mono kept)
    termination_by structural read

  theorem FieldsRead.mono {before after : Array Instruction}
      (kept : ∀ (reference : Nat) (instruction : Instruction), before[reference]? = some instruction → after[reference]? = some instruction)
      {trees : List ExpressionTree} {codes : List Code} (read : FieldsRead before trees codes) : FieldsRead after trees codes :=
    match read with
    | .nil => .nil
    | .cons head tail => .cons (head.mono kept) (tail.mono kept)
    termination_by structural read

  theorem ClausesRead.mono {before after : Array Instruction}
      (kept : ∀ (reference : Nat) (instruction : Instruction), before[reference]? = some instruction → after[reference]? = some instruction)
      {trees : List (MatchPattern × ExpressionTree)} {clauses : List Clause}
      (read : ClausesRead before trees clauses) : ClausesRead after trees clauses :=
    match read with
    | .nil => .nil
    | .cons head tail => .cons (head.mono kept) (tail.mono kept)
    termination_by structural read
end

#print axioms Reads.mono
#print axioms FieldsRead.mono
#print axioms ClausesRead.mono

end Mettapedia.Languages.OCaml.ExpressionTree
