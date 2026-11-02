import Mettapedia.Languages.OCaml.Assembly

/-! Concrete expression syntax before postorder code allocation. Variable
indices and anonymous pattern slots are already resolved; constructor and
child order remain data. Assembly uses the existing builder operations. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

inductive ExpressionTree where
  | literal (value : Literal)
  | variableRef (index : Nat)
  | lambda (parameter : MatchPattern) (body : ExpressionTree)
  | apply (function argument : ExpressionTree)
  | letValue (pattern : MatchPattern) (value body : ExpressionTree)
  | letRecursive (definitions : List ExpressionTree) (body : ExpressionTree)
  | branch (condition yes no : ExpressionTree)
  | andThen (left right : ExpressionTree)
  | orElse (left right : ExpressionTree)
  | tuple (fields : List ExpressionTree)
  | cons (head tail : ExpressionTree)
  | variant (typeId constructor : Nat) (fields : List ExpressionTree)
  | matchValue (scrutinee : ExpressionTree) (clauses : List (MatchPattern × ExpressionTree))
  | primitive (operator : Primitive) (arguments : List ExpressionTree)
  deriving Repr

namespace ExpressionTree

def integer (value : Int) : ExpressionTree := .literal (.integer value)
def boolean (value : Bool) : ExpressionTree := .literal (.boolean value)
def nil : ExpressionTree := .literal .nil
def unit : ExpressionTree := .literal .unit

@[irreducible] def compile : ExpressionTree → Assembly.Expression
  | .literal value => Assembly.literal value
  | .variableRef index => Assembly.variableRef index
  | .lambda parameter body => Assembly.lambda parameter body.compile
  | .apply function argument => Assembly.apply function.compile argument.compile
  | .letValue pattern value body => Assembly.letValue pattern value.compile body.compile
  | .letRecursive definitions body => Assembly.letRecursive (definitions.map compile) body.compile
  | .branch condition yes no => Assembly.branch condition.compile yes.compile no.compile
  | .andThen left right => Assembly.andThen left.compile right.compile
  | .orElse left right => Assembly.orElse left.compile right.compile
  | .tuple fields => Assembly.tuple (fields.map compile)
  | .cons head tail => Assembly.cons head.compile tail.compile
  | .variant typeId constructor fields => Assembly.variant typeId constructor (fields.map compile)
  | .matchValue scrutinee clauses =>
      Assembly.matchValue scrutinee.compile (clauses.map fun clause => (clause.1, clause.2.compile))
  | .primitive operator arguments => Assembly.primitive operator (arguments.map compile)
termination_by tree => sizeOf tree
decreasing_by
  all_goals first
    | decreasing_trivial
    | (have member := List.sizeOf_lt_of_mem (show clause ∈ clauses from by assumption)
       have smaller : sizeOf clause.2 < sizeOf clause := by cases clause; simp; omega
       simp only [ExpressionTree.matchValue.sizeOf_spec]
       omega)

def assemble (expression : ExpressionTree) (constructors : List Constructor := []) : Program :=
  Assembly.assemble expression.compile constructors

end ExpressionTree

structure TreeProgram where
  constructors : List Constructor := []
  expression : ExpressionTree

@[irreducible] def TreeProgram.assemble (program : TreeProgram) : Program :=
  program.expression.assemble program.constructors

end Mettapedia.Languages.OCaml
