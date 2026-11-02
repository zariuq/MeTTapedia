import Mathlib.Data.List.Basic

/-!
# Scalar values and predicate results

Integer/symbol data and Boolean predicates have different result sorts.
Arithmetic may refuse a symbol; it never interprets a predicate as 0 or 1.
Conditionals evaluate only their selected branch. The parameterized read
environment is deliberately separate from any source language's bindings.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TypedScalar

inductive Data
  | integer (value : Int)
  | symbol (name : String)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Kind | data | test
  deriving DecidableEq

abbrev Value : Kind → Type
  | .data => Data
  | .test => Bool

def valueEq : {left right : Kind} → Value left → Value right → Bool
  | .data, .data, a, b => a == b
  | .test, .test, a, b => a == b
  | .data, .test, _, _ => false
  | .test, .data, _, _ => false

inductive Binary : Kind → Kind → Kind → Type
  | add : Binary .data .data .data
  | sub : Binary .data .data .data
  | lt : Binary .data .data .test
  | le : Binary .data .data .test
  | gt : Binary .data .data .test
  | ge : Binary .data .data .test
  | equal {left right : Kind} : Binary left right .test

def Binary.name : {a b c : Kind} → Binary a b c → String
  | _, _, _, .add => "+"
  | _, _, _, .sub => "-"
  | _, _, _, .lt => "<"
  | _, _, _, .le => "<="
  | _, _, _, .gt => ">"
  | _, _, _, .ge => ">="
  | _, _, _, .equal => "=="

def Binary.eval : {a b c : Kind} → Binary a b c → Value a → Value b → Option (Value c)
  | _, _, _, .add, .integer x, .integer y => some (.integer (x + y))
  | _, _, _, .sub, .integer x, .integer y => some (.integer (x - y))
  | _, _, _, .lt, .integer x, .integer y => some (decide (x < y))
  | _, _, _, .le, .integer x, .integer y => some (decide (x ≤ y))
  | _, _, _, .gt, .integer x, .integer y => some (decide (x > y))
  | _, _, _, .ge, .integer x, .integer y => some (decide (x ≥ y))
  | _, _, _, .equal, x, y => some (valueEq x y)
  | _, _, _, .add, _, _ => none
  | _, _, _, .sub, _, _ => none
  | _, _, _, .lt, _, _ => none
  | _, _, _, .le, _, _ => none
  | _, _, _, .gt, _, _ => none
  | _, _, _, .ge, _, _ => none

inductive Expr (Slot : Type) : Kind → Type
  | literal (value : Data) : Expr Slot .data
  | boolean (value : Bool) : Expr Slot .test
  | read (slot : Slot) : Expr Slot .data
  | binary {a b c : Kind} (op : Binary a b c) (left : Expr Slot a) (right : Expr Slot b) : Expr Slot c
  | branch {kind : Kind} (test : Expr Slot .test) (yes no : Expr Slot kind) : Expr Slot kind

def Expr.eval {Slot : Type} (locals : Slot → Data) : {kind : Kind} → Expr Slot kind → Option (Value kind)
  | _, .literal value => some value
  | _, .boolean value => some value
  | _, .read slot => some (locals slot)
  | _, .binary op left right => do
      let x ← left.eval locals
      let y ← right.eval locals
      op.eval x y
  | _, .branch test yes no => do
      let chosen ← test.eval locals
      if chosen then yes.eval locals else no.eval locals

def Expr.reads {Slot : Type} : {kind : Kind} → Expr Slot kind → List Slot
  | _, .literal _ | _, .boolean _ => []
  | _, .read slot => [slot]
  | _, .binary _ left right => left.reads ++ right.reads
  | _, .branch test yes no => test.reads ++ yes.reads ++ no.reads

theorem Expr.eval_agrees {Slot : Type} {kind : Kind} (expr : Expr Slot kind)
    (first second : Slot → Data) (agree : ∀ slot ∈ expr.reads, first slot = second slot) :
    expr.eval first = expr.eval second := by
  induction expr with
  | literal => rfl
  | boolean => rfl
  | read slot => simp only [eval, agree slot (by simp [reads])]
  | binary op left right ihl ihr =>
      rw [eval, eval, ihl (by intro slot member; exact agree slot (by simp [reads, member])),
        ihr (by intro slot member; exact agree slot (by simp [reads, member]))]
  | branch test yes no iht ihy ihn =>
      rw [eval, eval, iht (by intro slot member; exact agree slot (by simp [reads, member])),
        ihy (by intro slot member; exact agree slot (by simp [reads, member])),
        ihn (by intro slot member; exact agree slot (by simp [reads, member]))]

namespace Controls

def nestedComparison : Expr Unit .test :=
  .binary .equal (.binary .lt (.literal (.integer 0)) (.literal (.integer 2)))
    (.literal (.integer 1))

theorem predicates_are_not_integer_values : nestedComparison.eval (fun _ => .integer 0) = some false := by decide

theorem unused_bad_branch_is_not_evaluated :
    (Expr.branch (.boolean true) (.literal (.integer 7))
      (.binary .add (.literal (.symbol "abc")) (.literal (.integer 1))) : Expr Unit .data).eval
      (fun _ => .integer 0) = some (.integer 7) := by decide

theorem symbol_arithmetic_refuses : Binary.add.eval (.symbol "abc") (.integer 1) = none := rfl

end Controls
end Mettapedia.Machines.TypedScalar
