import Mettapedia.Languages.CHR.Syntax

/-! Static admission of ground CHR programs. Predicate declarations retain
arity, guards read head variables, and body-local assignments extend the
available variables in goal order. Numeric type errors remain explicit
runtime faults: CHR constraints themselves are not numerically typed. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR

def IntExpr.variables : CHR.IntExpr → List Nat
  | .literal _ => []
  | .index idx => [idx]
  | .operation _ left right => left.variables ++ right.variables

def Guard.variables : CHR.Guard → List Nat
  | .identical left right | .distinct left right => left.variables ++ right.variables
  | .compare _ left right => left.variables ++ right.variables

namespace Admission

def declared (program : Program) (head : Head) : Bool :=
  program.declarations.any fun declaration => declaration.name == head.name && declaration.arity == head.arguments.length

def available (bound read : List Nat) : Bool := read.all (bound.contains ·)

inductive Diagnostic where
  | duplicateDeclaration (declaration : Declaration)
  | emptyHead (rule : Nat)
  | undeclaredHead (rule : Nat) (head : Head)
  | unboundGuard (rule : Nat) (guard : CHR.Guard)
  | unboundGoal (rule : Nat) (goal : Goal)
  | undeclaredGoal (rule : Nat) (head : Head)
  deriving Repr, DecidableEq, BEq

def goalsDiagnostic (program : Program) (rule : Nat) : List Nat → List Goal → Option Diagnostic
  | _, [] => none
  | bound, goal :: rest => match goal with
      | .tell head =>
          if !declared program head then some (.undeclaredGoal rule head)
          else if !available bound head.variables then some (.unboundGoal rule goal)
          else goalsDiagnostic program rule bound rest
      | .assign index expression =>
          if !available bound expression.variables then some (.unboundGoal rule goal)
          else goalsDiagnostic program rule (index :: bound) rest
      | .fail => goalsDiagnostic program rule bound rest

def ruleDiagnostic (program : Program) (index : Nat) (rule : Rule) : Option Diagnostic := do
  if rule.heads.isEmpty then some (.emptyHead index) else
    match rule.heads.find? (fun head => !declared program head) with
    | some head => some (.undeclaredHead index head)
    | none => match rule.guards.find? (fun guard => !available rule.variables guard.variables) with
        | some guard => some (.unboundGuard index guard)
        | none => goalsDiagnostic program index rule.variables rule.body

def diagnose (program : Program) : Option Diagnostic :=
  match program.declarations.zipIdx.find? (fun (declaration,index) =>
      (program.declarations.take index).contains declaration) with
  | some (declaration,_) => some (.duplicateDeclaration declaration)
  | none => program.rules.zipIdx.findSome? fun (rule,index) => ruleDiagnostic program index rule

end Admission
end Mettapedia.Languages.CHR
