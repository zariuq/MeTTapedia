import Mettapedia.Languages.OCaml.ExpressionTree

/-! Values for expression-tree evaluation. Closures retain source bodies or
recursive definitions, with no code-arena address. Primitive operands expose
data structure and the presence of a function, which is exactly what the
shared primitive profile observes. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

inductive TreeFunction where
  | lambda (parameter : MatchPattern) (body : ExpressionTree)
  | recursive (definitions : List ExpressionTree) (slot : Nat)
  deriving Repr

inductive TreeValue where
  | literal (value : Literal)
  | tuple (fields : List TreeValue)
  | cons (head tail : TreeValue)
  | variant (typeId constructor : Nat) (fields : List TreeValue)
  | closure (function : TreeFunction) (captured : List TreeValue)
  deriving Repr

abbrev TreeEnvironment := List TreeValue
abbrev TreeResult := Except Fault TreeValue

def extendTree (environment bindings : TreeEnvironment) : TreeEnvironment := bindings.reverse ++ environment

def recursiveTreeBindings (definitions : List ExpressionTree) (captured : TreeEnvironment) : List TreeValue :=
  (List.range definitions.length).map fun slot => .closure (.recursive definitions slot) captured

def recursiveTreeEnvironment (definitions : List ExpressionTree) (captured : TreeEnvironment) : TreeEnvironment :=
  extendTree captured (recursiveTreeBindings definitions captured)

/-- Operand-only view: function identity and captured values are unobservable
to the primitive profile, whose function comparison raises a language fault.
This view supplies no function execution or closure-compilation operation. -/
def TreeValue.primitiveOperand : TreeValue → Value
  | .literal value => .literal value
  | .tuple fields => .tuple (fields.map primitiveOperand)
  | .cons head tail => .cons head.primitiveOperand tail.primitiveOperand
  | .variant typeId constructor fields => .variant typeId constructor (fields.map primitiveOperand)
  | .closure _ _ => .closure (.lambda 0) []

end Mettapedia.Languages.OCaml
