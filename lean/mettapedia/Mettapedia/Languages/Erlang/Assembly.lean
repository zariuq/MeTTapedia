import Mettapedia.Languages.Erlang.Syntax

/-! Postorder assembly of the independent Erlang arena. This allocates code
references; it is neither a source reader nor an evaluator. Syntax/binding
frontends can share this allocation interface. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang.Assembly

abbrev Builder := StateM (Array Instruction)
abbrev Expression := Builder Code

def emit (instruction : Instruction) : Expression := do
  let code ← get
  set (code.push instruction)
  pure code.size

def literal (value : Literal) : Expression := emit (.literal value)
def integer (value : Int) : Expression := literal (.integer value)
def atom (name : String) : Expression := literal (.atom name)
def nil : Expression := literal .nil
def variableRef (index : Nat) : Expression := emit (.variable index)
def lambda (arity : Nat) (body : Expression) : Expression := do emit (.lambda arity (← body))
def apply (function : Expression) (arguments : List Expression) : Expression := do
  let function ← function
  emit (.apply function (← arguments.mapM id))
def letValues (arity : Nat) (argument body : Expression) : Expression := do
  let argument ← argument
  emit (.letValues arity argument (← body))
def letRecursive (definitions : List (Nat × Expression)) (body : Expression) : Expression := do
  let definitions ← definitions.mapM fun (arity, body) => do pure (FunctionDefinition.mk arity (← body))
  emit (.letRecursive definitions (← body))
def sequence (first second : Expression) : Expression := do
  let first ← first
  emit (.sequence first (← second))
def values (fields : List Expression) : Expression := do emit (.values (← fields.mapM id))
def tuple (fields : List Expression) : Expression := do emit (.tuple (← fields.mapM id))
def cons (head tail : Expression) : Expression := do
  let head ← head
  emit (.cons head (← tail))
def caseValues (argument : Expression) (clauses : List (List MatchPattern × Expression × Expression)) : Expression := do
  let argument ← argument
  let clauses ← clauses.mapM fun (patterns, guard, body) => do
    let guard ← guard
    pure (Clause.mk patterns guard (← body))
  emit (.caseValues argument clauses)
def primitive (operator : Primitive) (arguments : List Expression) : Expression := do
  emit (.primitive operator (← arguments.mapM id))
def actor (operation : ActorOperation) (arguments : List Expression) : Expression := do
  emit (.actor operation (← arguments.mapM id))
def matchFail (reason : Expression) : Expression := do emit (.matchFail (← reason))

def integers : List Int → Expression
  | [] => nil
  | head :: tail => cons (integer head) (integers tail)

def assemble (expression : Expression) : Program :=
  let (entry, code) := expression.run #[]
  ⟨code, entry⟩

theorem emit_reference (instruction : Instruction) (code : Array Instruction) :
    ((emit instruction).run code).1 = code.size := rfl

theorem emit_installed (instruction : Instruction) (code : Array Instruction) :
    ((emit instruction).run code).2[code.size]? = some instruction := by
  change (code.push instruction)[code.size]? = some instruction
  simp

end Mettapedia.Languages.Erlang.Assembly
