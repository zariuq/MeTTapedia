import Mettapedia.Languages.OCaml.AssemblyPreservation

/-! Every expression-tree constructor assembles to its independently
specified instruction graph while preserving all earlier arena entries.
Allocation and evaluation order are separate: the latter remains the
independent OCaml operational judgment. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.ExpressionTree

open Assembly

mutual
  theorem compile_correct (tree : ExpressionTree) : Builds tree tree.compile :=
    match tree with
    | .literal value => by
      simpa only [compile, Assembly.literal] using builds_emit (.literal value) (.literal value) (fun _ _ row => .literal row)
    | .variableRef index => by
      simpa only [compile, Assembly.variableRef] using builds_emit (.variableRef index) (.variable index) (fun _ _ row => .variable row)
    | .lambda pattern body => by
      simpa only [compile, Assembly.lambda] using builds_unary (parent := .lambda pattern body)
        (compile_correct body) (.lambda pattern) (fun _ _ _ row child => .lambda row child)
    | .apply function argument => by
      simpa only [compile, Assembly.apply] using builds_binary (parent := .apply function argument)
        (compile_correct function) (compile_correct argument) Instruction.apply (fun _ _ _ _ row left right => .apply row left right)
    | .letValue pattern value body => by
      simpa only [compile, Assembly.letValue] using builds_binary (parent := .letValue pattern value body)
        (compile_correct value) (compile_correct body) (.letValue pattern) (fun _ _ _ _ row left right => .letValue row left right)
    | .letRecursive definitions body => by
      simpa only [compile] using builds_functions (compile_fields_correct definitions) (compile_correct body)
    | .branch condition yes no => by
      simpa only [compile, Assembly.branch] using builds_ternary (parent := .branch condition yes no)
        (compile_correct condition) (compile_correct yes) (compile_correct no) Instruction.branch
        (fun _ _ _ _ _ row test positive negative => .branch row test positive negative)
    | .andThen left right => by
      simpa only [compile, Assembly.andThen] using builds_binary (parent := .andThen left right)
        (compile_correct left) (compile_correct right) Instruction.andThen (fun _ _ _ _ row first second => .andThen row first second)
    | .orElse left right => by
      simpa only [compile, Assembly.orElse] using builds_binary (parent := .orElse left right)
        (compile_correct left) (compile_correct right) Instruction.orElse (fun _ _ _ _ row first second => .orElse row first second)
    | .tuple fields => by
      simpa only [compile, Assembly.tuple] using builds_fields_node (compile_fields_correct fields)
        (.tuple fields) Instruction.tuple (fun _ _ _ row children => .tuple row children)
    | .cons head tail => by
      simpa only [compile, Assembly.cons] using builds_binary (parent := .cons head tail)
        (compile_correct head) (compile_correct tail) Instruction.cons (fun _ _ _ _ row first second => .cons row first second)
    | .variant typeId constructor fields => by
      simpa only [compile, Assembly.variant] using builds_fields_node (compile_fields_correct fields)
        (.variant typeId constructor fields) (.variant typeId constructor) (fun _ _ _ row children => .variant row children)
    | .matchValue scrutinee clauses => by
      simpa only [compile] using builds_match (compile_correct scrutinee) (compile_clauses_correct clauses)
    | .primitive operator arguments => by
      simpa only [compile, Assembly.primitive] using builds_fields_node (compile_fields_correct arguments)
        (.primitive operator arguments) (.primitive operator) (fun _ _ _ row children => .primitive row children)
    termination_by sizeOf tree

  theorem compile_fields_correct (trees : List ExpressionTree) : BuildsFields trees (trees.map compile) :=
    match trees with
    | [] => builds_fields_nil
    | first :: rest => builds_fields_cons (compile_correct first) (compile_fields_correct rest)
    termination_by sizeOf trees

  theorem compile_clauses_correct (clauses : List (MatchPattern × ExpressionTree)) :
      BuildsClauses clauses (clauses.map fun clause => (clause.1, clause.2.compile)) :=
    match clauses with
    | [] => builds_clauses_nil
    | (pattern, body) :: rest => builds_clauses_cons (compile_correct body) (compile_clauses_correct rest)
    termination_by sizeOf clauses
end

theorem assembled_reads (tree : ExpressionTree) (constructors : List Constructor) :
    Reads (tree.assemble constructors).code tree (tree.assemble constructors).entry := (compile_correct tree #[]).2

theorem assemble_preserves_declarations (tree : ExpressionTree) (constructors : List Constructor) :
    (tree.assemble constructors).constructors = constructors := rfl

#print axioms compile_correct
#print axioms compile_fields_correct
#print axioms compile_clauses_correct
#print axioms assembled_reads
#print axioms assemble_preserves_declarations

end Mettapedia.Languages.OCaml.ExpressionTree
