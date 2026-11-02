import Mettapedia.Languages.OCaml.Syntax

/-! Ordinary postorder assembly for indexed code. Child builders finish before
their instruction is installed. This is neither a source parser nor a runtime
interpreter; syntax frontends can use the same code-allocation interface. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.Assembly

abbrev Builder := StateM (Array Instruction)
abbrev Expression := Builder Code

def emit (instruction : Instruction) : Expression := do
  let code ← get
  set (code.push instruction)
  pure code.size

def literal (value : Literal) : Expression := emit (.literal value)
def integer (value : Int) : Expression := literal (.integer value)
def boolean (value : Bool) : Expression := literal (.boolean value)
def nil : Expression := literal .nil
def unit : Expression := literal .unit
def variableRef (index : Nat) : Expression := emit (.variable index)

def lambda (parameter : MatchPattern) (body : Expression) : Expression := do
  emit (.lambda parameter (← body))

def apply (function argument : Expression) : Expression := do
  let function ← function
  let argument ← argument
  emit (.apply function argument)

def letValue (pattern : MatchPattern) (value body : Expression) : Expression := do
  let value ← value
  let body ← body
  emit (.letValue pattern value body)

def letRecursive (definitions : List Expression) (body : Expression) : Expression := do
  let definitions ← definitions.mapM id
  let body ← body
  emit (.letRecursive definitions body)

def branch (condition yes no : Expression) : Expression := do
  let condition ← condition
  let yes ← yes
  let no ← no
  emit (.branch condition yes no)

def andThen (left right : Expression) : Expression := do emit (.andThen (← left) (← right))
def orElse (left right : Expression) : Expression := do emit (.orElse (← left) (← right))
def tuple (fields : List Expression) : Expression := do emit (.tuple (← fields.mapM id))
def cons (head tail : Expression) : Expression := do emit (.cons (← head) (← tail))

def variant (typeId constructor : Nat) (fields : List Expression) : Expression := do
  emit (.variant typeId constructor (← fields.mapM id))

def matchValue (scrutinee : Expression) (clauses : List (MatchPattern × Expression)) : Expression := do
  let scrutinee ← scrutinee
  let clauses ← clauses.mapM fun (pattern, body) => do pure (Clause.mk pattern (← body))
  emit (.matchValue scrutinee clauses)

def primitive (operator : Primitive) (arguments : List Expression) : Expression := do
  emit (.primitive operator (← arguments.mapM id))

def integers : List Int → Expression
  | [] => nil
  | head :: tail => cons (integer head) (integers tail)

def assemble (expression : Expression) (constructors : List Constructor := []) : Program :=
  let (entry, code) := expression.run #[]
  ⟨constructors, code, entry⟩

theorem emit_reference (instruction : Instruction) (code : Array Instruction) :
    ((emit instruction).run code).1 = code.size := rfl

theorem emit_installed (instruction : Instruction) (code : Array Instruction) :
    ((emit instruction).run code).2[code.size]? = some instruction := by
  change (code.push instruction)[code.size]? = some instruction
  simp

end Mettapedia.Languages.OCaml.Assembly
