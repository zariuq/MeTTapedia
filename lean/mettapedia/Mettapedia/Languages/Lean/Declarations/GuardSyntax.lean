import Mathlib.Data.Fin.Basic

/-!
# Scoped propositions of constructor proof fields

Field variables and bound variables share a de Bruijn scope. A product binds
one variable in its body and none in its domain. This syntax is separate from
the first-order index expressions admitted by a family profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.GuardSyntax

inductive Term : Nat → Type where
  | var {depth : Nat} (position : Fin depth) : Term depth
  | name {depth : Nat} (identifier : String) : Term depth
  | app {depth : Nat} (function argument : Term depth) : Term depth
  | pi {depth : Nat} (domain : Term depth) (body : Term (depth + 1)) : Term depth
  | project {depth : Nat} (owner : String) (field : Nat) (record : Term depth) : Term depth
  deriving Repr, DecidableEq

def liftRenaming {n m : Nat} (rename : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun position => (rename position).succ)

def Term.rename {n m : Nat} (rename : Fin n → Fin m) : Term n → Term m
  | .var position => .var (rename position)
  | .name identifier => .name identifier
  | .app function argument => .app (function.rename rename) (argument.rename rename)
  | .pi domain body => .pi (domain.rename rename) (body.rename (liftRenaming rename))
  | .project owner field record => .project owner field (record.rename rename)

structure Semantics (Value : Type) where
  constant : String → Value
  apply : Value → Value → Value
  product : Value → (Value → Value) → Value
  project : String → Nat → Value → Value

def Term.eval {Value : Type} (semantics : Semantics Value) {depth : Nat}
    (environment : Fin depth → Value) : Term depth → Value
  | .var position => environment position
  | .name identifier => semantics.constant identifier
  | .app function argument => semantics.apply (function.eval semantics environment)
      (argument.eval semantics environment)
  | .pi domain body => semantics.product (domain.eval semantics environment)
      (fun value => body.eval semantics (Fin.cases value environment))
  | .project owner field record => semantics.project owner field (record.eval semantics environment)

/-- Changing the syntactic scope and reindexing the environment commute. -/
theorem Term.eval_rename {Value : Type} (semantics : Semantics Value) {n m : Nat}
    (term : Term n) (rename : Fin n → Fin m) (environment : Fin m → Value) :
    (term.rename rename).eval semantics environment =
      term.eval semantics (environment ∘ rename) := by
  induction term generalizing m with
  | var => rfl
  | name => rfl
  | app function argument hf ha => simp only [Term.rename, Term.eval, hf, ha]
  | project owner field record ih => simp only [Term.rename, Term.eval, ih]
  | pi domain body hd hb =>
      simp only [Term.rename, Term.eval, hd, hb]
      apply congrArg (semantics.product _)
      funext value
      apply congrArg (fun env => body.eval semantics env)
      funext position
      exact Fin.cases rfl (fun _ => rfl) position

end Mettapedia.Languages.Lean.Declarations.GuardSyntax
