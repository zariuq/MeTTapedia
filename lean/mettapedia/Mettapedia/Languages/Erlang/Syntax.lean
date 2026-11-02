import Mathlib.Data.List.Basic

/-! Indexed code for the sequential Core Erlang component. Code bodies live
in an immutable arena; closures carry a reference and an environment, not a
source grammar tree. Environments count from the head. A vector of binders
is pushed in reverse source order, so its last variable has index zero.

Return vectors are distinct from tuple values. This matters for Core's
multi-value lets and the two results of recv_peek_message. Source lowering,
formation and machine realization are separate interfaces. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

abbrev Code := Nat

inductive Literal where
  | atom (name : String)
  | integer (value : Int)
  | nil
  deriving Repr, DecidableEq, BEq

inductive MatchPattern where
  | bind
  | wildcard
  | literal (value : Literal)
  | pinned (index : Nat)
  | alias (pattern : MatchPattern)
  | tuple (fields : List MatchPattern)
  | cons (head tail : MatchPattern)
  deriving Repr, BEq

def MatchPattern.binders : MatchPattern → Nat
  | .bind => 1
  | .wildcard | .literal _ | .pinned _ => 0
  | .alias pattern => 1 + pattern.binders
  | .tuple fields => (fields.map MatchPattern.binders).sum
  | .cons head tail => head.binders + tail.binders

inductive Primitive where
  | add | subtract | multiply | divide | remainder | negate
  | equal | different | less | lessEqual | greater | greaterEqual
  | isInteger | isAtom | isTuple | isList | isPid | isFunction | isFunctionArity
  | andBool | orBool | xorBool | notBool
  deriving Repr, DecidableEq, BEq

inductive ActorOperation where
  | self | spawn | send
  | peekMessage | nextMessage | removeMessage | waitInfinity
  deriving Repr, DecidableEq, BEq

structure Clause where
  patterns : List MatchPattern
  guard : Code
  body : Code
  deriving Repr, BEq

structure FunctionDefinition where
  arity : Nat
  body : Code
  deriving Repr, DecidableEq, BEq

inductive Instruction where
  | literal (value : Literal)
  | variable (index : Nat)
  | lambda (arity : Nat) (body : Code)
  | apply (function : Code) (arguments : List Code)
  | letValues (arity : Nat) (argument body : Code)
  | letRecursive (definitions : List FunctionDefinition) (body : Code)
  | sequence (first second : Code)
  | values (fields : List Code)
  | tuple (fields : List Code)
  | cons (head tail : Code)
  | caseValues (argument : Code) (clauses : List Clause)
  | primitive (operator : Primitive) (arguments : List Code)
  | actor (operation : ActorOperation) (arguments : List Code)
  | matchFail (reason : Code)
  deriving Repr, BEq

structure Program where
  code : Array Instruction
  entry : Code
  deriving Repr

def Program.instruction? (program : Program) (reference : Code) : Option Instruction :=
  program.code[reference]?

inductive FunctionRef where
  | lambda (reference : Code)
  | recursive (group : Code) (slot : Nat)
  deriving Repr, DecidableEq, BEq

inductive Value where
  | literal (value : Literal)
  | pid (identity : Nat)
  | tuple (fields : List Value)
  | cons (head tail : Value)
  | closure (arity : Nat) (function : FunctionRef) (captured : List Value)
  deriving Repr

mutual
  def Value.sameTerm : Value → Value → Bool
    | .literal left, .literal right => decide (left = right)
    | .pid left, .pid right => decide (left = right)
    | .tuple left, .tuple right => Value.sameTerms left right
    | .cons head tail, .cons first rest => head.sameTerm first && tail.sameTerm rest
    | .closure arity function captured, .closure otherArity other environment =>
        decide (arity = otherArity ∧ function = other) && Value.sameTerms captured environment
    | _, _ => false

  def Value.sameTerms : List Value → List Value → Bool
    | [], [] => true
    | head :: tail, first :: rest => head.sameTerm first && Value.sameTerms tail rest
    | _, _ => false
end

instance : BEq Value where beq := Value.sameTerm

/-- Structural identity in the indexed IR. Native closure/identity profile
correspondence is a separate obligation; this theorem licenses no foreign
runtime identity comparison. -/
theorem Value.sameTerm_eq_true_iff (left : Value) :
    ∀ right, left.sameTerm right = true ↔ left = right := by
  refine Value.rec
    (motive_1 := fun left => ∀ right, left.sameTerm right = true ↔ left = right)
    (motive_2 := fun left => ∀ right, Value.sameTerms left right = true ↔ left = right)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro literal right
    cases right <;> simp [Value.sameTerm]
  · intro identity right
    cases right <;> simp [Value.sameTerm]
  · intro fields ih right
    cases right <;> simp [Value.sameTerm, ih]
  · intro head tail firstIH restIH right
    cases right <;> simp [Value.sameTerm, firstIH, restIH]
  · intro arity function captured ih right
    cases right <;> simp [Value.sameTerm, ih, and_assoc]
  · intro right
    cases right <;> simp [Value.sameTerms]
  · intro head tail firstIH restIH right
    cases right <;> simp [Value.sameTerms, firstIH, restIH]

abbrev Environment := List Value

def extend (environment bindings : List Value) : Environment := bindings.reverse ++ environment

def recursiveBindings (group : Code) (definitions : List FunctionDefinition) (captured : Environment) : List Value :=
  definitions.zipIdx.map fun (definition, slot) => .closure definition.arity (.recursive group slot) captured

def recursiveEnvironment (group : Code) (definitions : List FunctionDefinition) (captured : Environment) : Environment :=
  extend captured (recursiveBindings group definitions captured)

inductive Fault where
  | badarith
  | badarg
  | badfun (value : Value)
  | badarity (function : Value) (arguments : List Value)
  | caseClause (values : List Value)
  | matchFail (reason : Value)
  deriving Repr, BEq

inductive InternalError where
  | missingCode (reference : Code)
  | unboundVariable (index : Nat)
  | invalidRecursiveGroup (group : Code) (slot : Nat)
  | returnArity (expected actual : Nat)
  | comparisonProfileRequired (left right : Value)
  | effectfulGuard
  deriving Repr, BEq

abbrev Result := Except Fault (List Value)

instance : BEq Result where
  beq first second := match first, second with
    | .ok left, .ok right => left == right
    | .error left, .error right => left == right
    | _, _ => false

def boolean (value : Bool) : Value := .literal (.atom (if value then "true" else "false"))

def boolean? : Value → Option Bool
  | .literal (.atom "true") => some true
  | .literal (.atom "false") => some false
  | _ => none

end Mettapedia.Languages.Erlang
