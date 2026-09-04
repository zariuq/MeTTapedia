import Mathlib.Data.Fin.Basic

/-!
# Finitary one-sorted signatures and terms

This is the syntax layer of universal algebra.  It contains no operational,
modal, proof-authority, or Prime-specific structure.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

universe u

/-- A one-sorted finitary signature. -/
structure Signature : Type (u + 1) where
  Operation : Type u
  arity : Operation → Nat

variable {S : Signature.{u}}

/-- Terms over `S`, with variables indexed by natural numbers. -/
inductive Term (S : Signature.{u}) : Type u where
  | var : Nat → Term S
  | op : (operation : S.Operation) →
      (Fin (S.arity operation) → Term S) → Term S

instance instDecidableEq [DecidableEq S.Operation] : DecidableEq (Term S)
  | .var left, .var right =>
      decidable_of_iff (left = right) (by simp)
  | .op leftOperation leftArguments, .op rightOperation rightArguments =>
      if operationEq : leftOperation = rightOperation then
        letI : DecidableEq (Term S) := instDecidableEq
        decidable_of_iff
          (∀ position,
            leftArguments position = rightArguments
              (Fin.cast (congrArg S.arity operationEq) position)) (by
            subst operationEq
            simp [funext_iff])
      else
        .isFalse (by simp [operationEq])
  | .var _, .op _ _ | .op _ _, .var _ => .isFalse (by simp)

/-- Simultaneous substitution of terms for variables. -/
def Term.subst (substitution : Nat → Term S) : Term S → Term S
  | .var index => substitution index
  | .op operation arguments =>
      .op operation (fun i => (arguments i).subst substitution)

@[simp] theorem Term.subst_var (substitution : Nat → Term S) (index : Nat) :
    (Term.var index : Term S).subst substitution = substitution index := rfl

@[simp] theorem Term.subst_op (substitution : Nat → Term S)
    (operation : S.Operation) (arguments : Fin (S.arity operation) → Term S) :
    (Term.op operation arguments).subst substitution =
      .op operation (fun i => (arguments i).subst substitution) := rfl

@[simp] theorem Term.subst_variables :
    ∀ term : Term S, term.subst Term.var = term
  | .var _ => rfl
  | .op operation arguments => by
      simp only [Term.subst_op]
      congr 1
      funext i
      exact Term.subst_variables (arguments i)

end Mettapedia.UniversalAlgebra
