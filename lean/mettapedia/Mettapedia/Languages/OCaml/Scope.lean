import Mettapedia.Languages.OCaml.Syntax
import Mettapedia.Languages.OCaml.Primitives

/-! Formation checks for indexed code, independently of source parsing.
References descend in the code arena. Recursion goes through environment
bindings, not cyclic code arrays. This checks scope and data formation;
OCaml typing and source-to-code correspondence are separate contracts. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

def Program.constructorDeclared (program : Program) (typeId ordinal arity : Nat) : Bool :=
  program.constructors.any fun row =>
    row.typeId == typeId && row.ordinal == ordinal && row.arity == arity

def Literal.formed (strings : Bool) : Literal → Bool
  | .integer value => decide (-integerHalf ≤ value ∧ value < integerHalf)
  | .string _ => strings
  | _ => true

mutual
  def MatchPattern.formed (program : Program) (strings : Bool) : MatchPattern → Bool
    | .bind | .wildcard => true
    | .literal value => value.formed strings
    | .tuple fields => decide (2 ≤ fields.length) && patternsFormed program strings fields
    | .cons head tail => head.formed program strings && tail.formed program strings
    | .variant typeId constructor fields =>
        program.constructorDeclared typeId constructor fields.length && patternsFormed program strings fields

  def patternsFormed (program : Program) (strings : Bool) : List MatchPattern → Bool
    | [] => true
    | first :: rest => first.formed program strings && patternsFormed program strings rest
end

def Primitive.arity : Primitive → Nat
  | .negate | .notBool => 1
  | _ => 2

def Program.checkScopeAt (program : Program) (strings : Bool) : Nat → Code → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, reference, scope =>
      let child := fun code size => decide (code < reference) && program.checkScopeAt strings fuel code size
      match program.instruction? reference with
      | none => false
      | some instruction => match instruction with
          | .literal value => value.formed strings
          | .variable index => decide (index < scope)
          | .lambda pattern body =>
              pattern.formed program strings && child body (scope + pattern.binders)
          | .apply function argument => child function scope && child argument scope
          | .letValue pattern value body => pattern.formed program strings &&
              child value scope && child body (scope + pattern.binders)
          | .letRecursive definitions body =>
              !definitions.isEmpty && definitions.all (fun code =>
                (match program.instruction? code with | some (.lambda _ _) => true | _ => false) &&
                  child code (scope + definitions.length)) && child body (scope + definitions.length)
          | .branch condition yes no => child condition scope && child yes scope && child no scope
          | .andThen left right | .orElse left right | .cons left right =>
              child left scope && child right scope
          | .tuple fields => decide (2 ≤ fields.length) && fields.all (fun field => child field scope)
          | .variant typeId constructor fields =>
              program.constructorDeclared typeId constructor fields.length &&
                fields.all (fun field => child field scope)
          | .matchValue scrutinee clauses => child scrutinee scope && clauses.all (fun clause =>
              clause.pattern.formed program strings && child clause.body (scope + clause.pattern.binders))
          | .primitive operator arguments => decide (arguments.length = operator.arity) &&
              arguments.all (fun argument => child argument scope)

def Program.checkScope (program : Program) (strings : Bool := false) : Bool :=
  program.checkScopeAt strings (program.code.size + 1) program.entry 0

end Mettapedia.Languages.OCaml
