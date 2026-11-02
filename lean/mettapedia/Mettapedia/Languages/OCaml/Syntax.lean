import Mathlib.Data.List.Basic

/-! Source-independent indexed code for the pure OCaml core. Code bodies live
in the program arena; closures carry references and captured environments.
Indices in an environment count from its head. Pattern bindings and recursive
groups are pushed in reverse source order, so the last binder has index zero.
Formation, source lowering and runtime execution are separate interfaces. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

abbrev Code := Nat

inductive Literal where
  | integer (value : Int)
  | boolean (value : Bool)
  | unit
  | nil
  | string (bytes : List UInt8)
  deriving Repr, DecidableEq, BEq

inductive MatchPattern where
  | bind
  | wildcard
  | literal (value : Literal)
  | tuple (fields : List MatchPattern)
  | cons (head tail : MatchPattern)
  | variant (typeId constructor : Nat) (fields : List MatchPattern)
  deriving Repr, BEq

def MatchPattern.binders : MatchPattern → Nat
  | .bind => 1
  | .wildcard | .literal _ => 0
  | .tuple fields | .variant _ _ fields => (fields.map MatchPattern.binders).sum
  | .cons head tail => head.binders + tail.binders

inductive Primitive where
  | add | subtract | multiply | divide | modulo | negate
  | equal | different | less | lessEqual | greater | greaterEqual
  | notBool
  deriving Repr, DecidableEq, BEq

structure Clause where
  pattern : MatchPattern
  body : Code
  deriving Repr, BEq

inductive Instruction where
  | literal (value : Literal)
  | variable (index : Nat)
  | lambda (parameter : MatchPattern) (body : Code)
  | apply (function argument : Code)
  | letValue (pattern : MatchPattern) (value body : Code)
  | letRecursive (definitions : List Code) (body : Code)
  | branch (condition yes no : Code)
  | andThen (left right : Code)
  | orElse (left right : Code)
  | tuple (fields : List Code)
  | cons (head tail : Code)
  | variant (typeId constructor : Nat) (fields : List Code)
  | matchValue (scrutinee : Code) (clauses : List Clause)
  | primitive (operator : Primitive) (arguments : List Code)
  deriving Repr, BEq

structure Constructor where
  typeId : Nat
  ordinal : Nat
  arity : Nat
  deriving Repr, DecidableEq, BEq

structure Program where
  constructors : List Constructor := []
  code : Array Instruction
  entry : Code
  deriving Repr

def Program.instruction? (program : Program) (reference : Code) : Option Instruction :=
  program.code[reference]?

inductive FunctionRef where
  | lambda (code : Code)
  | recursive (group : Code) (slot : Nat)
  deriving Repr, DecidableEq, BEq

inductive Value where
  | literal (value : Literal)
  | tuple (fields : List Value)
  | cons (head tail : Value)
  | variant (typeId constructor : Nat) (fields : List Value)
  | closure (function : FunctionRef) (captured : List Value)
  deriving Repr, BEq

abbrev Environment := List Value

def extend (environment bindings : List Value) : Environment := bindings.reverse ++ environment

def recursiveBindings (group : Code) (definitions : List Code)
    (captured : Environment) : List Value :=
  (List.range definitions.length).map fun slot => .closure (.recursive group slot) captured

def recursiveEnvironment (group : Code) (definitions : List Code)
    (captured : Environment) : Environment :=
  extend captured (recursiveBindings group definitions captured)

inductive Fault where
  | divisionByZero
  | matchFailure
  | functionalComparison
  deriving Repr, DecidableEq, BEq

inductive InternalError where
  | missingCode (code : Code)
  | unboundVariable (index : Nat)
  | nonFunction (value : Value)
  | nonBoolean (value : Value)
  | invalidPrimitiveArguments (operator : Primitive) (arguments : List Value)
  | invalidRecursiveGroup (group : Code) (slot : Nat)
  | incomparableValues (left right : Value)
  | invalidConstructor (typeId constructor arity : Nat)
  | invalidTupleArity (arity : Nat)
  | unexpectedStop
  deriving Repr, BEq

abbrev Result := Except Fault Value

instance : BEq Result where
  beq first second := match first, second with
    | .ok left, .ok right => left == right
    | .error left, .error right => left == right
    | _, _ => false

end Mettapedia.Languages.OCaml
