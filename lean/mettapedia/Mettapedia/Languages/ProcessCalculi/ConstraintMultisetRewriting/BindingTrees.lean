import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationStore
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualSubstitution

/-!
# Ambient substitution on the existing abstract binding trees

The equation-store interface acts directly on the existing signature-indexed
ABT, through its proved single-sort bridge and capture-avoiding substitution.
Binder-bound indices are rigid within their binder; ambient indices may be
refined on either side of an equation.

This is an ambient-substitution profile, not a higher-order metavariable
unification algorithm. Contextual metavariable spines and beta/eta conversion
require their own solver and preservation laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BindingTrees

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

variable {Head : Type}

def action : SubstitutionAction (Term Head) (Nat → Term Head) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := Term.substituteMany
  identity := Term.idx
  compose := fun outer inner index => Term.substituteMany outer (inner index)
  apply_identity := Term.substituteMany_ids
  apply_compose := fun outer inner term => (Term.substituteMany_comp outer inner term).symm
  preserves := fun σ {_ _} same => congrArg (Term.substituteMany σ) same

namespace Controls

def lam (body : Term Nat) : Term Nat := .node 77 (.cons 1 body .nil)

theorem substitute_lam (σ : Nat → Term Nat) (body : Term Nat) :
    action.apply σ (lam body) = lam (Term.substituteMany (underBinders 1 σ) body) := by
  simp only [action, lam, substitute_node, substitute_fields_cons, substitute_fields_nil]

theorem bound_variable_stays_bound (σ : Nat → Term Nat) :
    action.apply σ (lam (.idx 0)) = lam (.idx 0) := by
  rw [substitute_lam, Term.substituteMany_idx, underBinders_eq]
  rfl

theorem ambient_variable_is_weakened (σ : Nat → Term Nat) :
    action.apply σ (lam (.idx 1)) = lam (Term.lift 0 1 (σ 0)) := by
  rw [substitute_lam, Term.substituteMany_idx, underBinders_eq]
  rfl

private theorem lifted_term_cannot_be_innermost (term : Term Nat) :
    Term.lift 0 1 term ≠ .idx 0 := by
  cases term <;> simp [Term.lift]

/-- A variable outside a lambda cannot be solved by capturing that lambda's
bound variable. The impossibility holds for every ambient substitution. -/
theorem undeclared_binder_capture_has_no_solution :
    ¬ action.Consistent [(lam (.idx 1), lam (.idx 0))] := by
  rintro ⟨σ, solved⟩
  have same := solved (lam (.idx 1), lam (.idx 0)) (by simp)
  change action.apply σ (lam (.idx 1)) = action.apply σ (lam (.idx 0)) at same
  rw [ambient_variable_is_weakened, bound_variable_stays_bound] at same
  have fields := (Term.node.inj same).2
  have body := (Fields.cons.inj fields).2.1
  exact lifted_term_cannot_be_innermost (σ 0) body

theorem ambient_application_under_binder_is_accepted :
    action.Consistent [(lam (.idx 1), lam (.node 42 .nil))] := by
  refine ⟨fun _ => .node 42 .nil, ?_⟩
  intro equation member
  have same : equation = (lam (.idx 1), lam (.node 42 .nil)) := by simpa using member
  subst equation
  rfl

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BindingTrees
