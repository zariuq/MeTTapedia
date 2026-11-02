import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedVariables
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# One global solution is a compatible family of per-use solutions, when uses are renamed apart

Uses `ScopedVariables.termAt` (schema locals copied into an activation scope,
captured variables kept) and `ScopedVariables.local_scope`. Each use `i` contributes its
equations, renamed into scope `scopeOf i`.

* With pairwise distinct scopes, one substitution solves every renamed use exactly when there is
  a family of per-use substitutions, each solving its own use, that agree on every captured
  (shared) variable. The global solution is glued from the family.
* Without distinct scopes the gluing fails: two uses of `p(X)` at `p(a)` and `p(b)` in the same
  scope have per-use solutions but no global one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedSolutionGluing

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

variable {signature : LPSignature} {Local Shared : Type} [DecidableEq Local] [DecidableEq Shared]

/-- A substitution solves the use's equations after they are copied into `scope`. -/
def Solves (σ : Subst (signature.withVars (ScopedVar Local ⊕ Shared))) (scope : Nat)
    (equations : List (Term (signature.withVars (Local ⊕ Shared)) × Term (signature.withVars (Local ⊕ Shared)))) :
    Prop :=
  ∀ e ∈ equations, σ.applyTerm (ScopedVariables.termAt scope e.1) = σ.applyTerm (ScopedVariables.termAt scope e.2)

open Classical in
/-- Glue a family: a local variable of scope `s` takes the value given by the use whose scope
is `s`; a captured variable takes the common value. -/
noncomputable def glued {n : Nat} (scopeOf : Fin n → Nat)
    (τ : Fin n → Subst (signature.withVars (ScopedVar Local ⊕ Shared))) :
    Subst (signature.withVars (ScopedVar Local ⊕ Shared))
  | .inl name => if h : ∃ i, scopeOf i = name.scope then τ h.choose (.inl name) else .var (.inl name)
  | .inr shared => if h : 0 < n then τ ⟨0, h⟩ (.inr shared) else .var (.inr shared)

theorem glued_agrees {n : Nat} (scopeOf : Fin n → Nat) (injective : Function.Injective scopeOf)
    (τ : Fin n → Subst (signature.withVars (ScopedVar Local ⊕ Shared)))
    (agree : ∀ i j (shared : Shared), τ i (.inr shared) = τ j (.inr shared))
    (i : Fin n) (term : Term (signature.withVars (Local ⊕ Shared))) :
    ∀ v ∈ (ScopedVariables.termAt (scopeOf i) term).freeVars, glued scopeOf τ v = τ i v := by
  intro v member
  cases v with
  | inl name =>
      have scopeEq : name.scope = scopeOf i := ScopedVariables.local_scope (scopeOf i) term name member
      have found : ∃ j, scopeOf j = name.scope := ⟨i, scopeEq.symm⟩
      have chosen : found.choose = i := injective (found.choose_spec.trans scopeEq)
      simp only [glued, dif_pos found, chosen]
  | inr shared =>
      have positive : 0 < n := i.pos
      simp only [glued, dif_pos positive]
      exact agree _ _ shared

/-- **Gluing.** With distinct scopes, a global solution exists exactly when a compatible family
of per-use solutions exists. -/
theorem glue {n : Nat} (scopeOf : Fin n → Nat) (injective : Function.Injective scopeOf)
    (uses : Fin n → List (Term (signature.withVars (Local ⊕ Shared)) × Term (signature.withVars (Local ⊕ Shared)))) :
    (∃ σ, ∀ i, Solves σ (scopeOf i) (uses i)) ↔
      ∃ τ : Fin n → Subst (signature.withVars (ScopedVar Local ⊕ Shared)),
        (∀ i, Solves (τ i) (scopeOf i) (uses i)) ∧ ∀ i j (shared : Shared), τ i (.inr shared) = τ j (.inr shared) := by
  constructor
  · rintro ⟨σ, solves⟩
    exact ⟨fun _ => σ, solves, fun _ _ _ => rfl⟩
  · rintro ⟨τ, solves, agree⟩
    refine ⟨glued scopeOf τ, fun i e member => ?_⟩
    rw [Subst.applyTerm_congr (glued_agrees scopeOf injective τ agree i e.1),
      Subst.applyTerm_congr (glued_agrees scopeOf injective τ agree i e.2)]
    exact solves i e member

/-! ## Separating example: one scope for two uses -/

abbrev base : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Unit
  functionArity _ := 1

abbrev SourceTerm := Term (base.withVars (Nat ⊕ Nat))

def X : SourceTerm := .var (.inl 0)
def constant (c : Nat) : SourceTerm := .const c

/-- Use `i` matches the schema variable `X` against the constant `i`. -/
def twoUses : Fin 2 → List (SourceTerm × SourceTerm) := fun i => [(X, constant i.val)]

def perUse : Fin 2 → Subst (base.withVars (ScopedVar Nat ⊕ Nat))
  | i, .inl _ => .const i.val
  | _, .inr _ => .const 5

theorem same_scope_has_a_compatible_family :
    (∀ i, Solves (perUse i) 7 (twoUses i)) ∧ ∀ i j (shared : Nat), perUse i (.inr shared) = perUse j (.inr shared) := by
  refine ⟨fun i e member => ?_, fun _ _ _ => rfl⟩
  have same : e = (X, constant i.val) := by simpa [twoUses] using member
  subst same
  rfl

theorem same_scope_has_no_global_solution :
    ¬ ∃ σ : Subst (base.withVars (ScopedVar Nat ⊕ Nat)), ∀ i, Solves σ 7 (twoUses i) := by
  rintro ⟨σ, solves⟩
  have zero := solves 0 (X, constant 0) (by simp [twoUses])
  have one := solves 1 (X, constant 1) (by simp [twoUses])
  have both : (Term.const 0 : Term (base.withVars (ScopedVar Nat ⊕ Nat))) = .const 1 :=
    zero.symm.trans one
  cases both

/-- With scopes `0` and `1` the same family glues. -/
theorem distinct_scopes_glue :
    ∃ σ : Subst (base.withVars (ScopedVar Nat ⊕ Nat)), ∀ i : Fin 2, Solves σ i.val (twoUses i) := by
  have family : ∀ i : Fin 2, Solves (perUse i) i.val (twoUses i) := by
    intro i e member
    have same : e = (X, constant i.val) := by simpa [twoUses] using member
    subst same
    rfl
  exact (glue (fun i : Fin 2 => i.val) Fin.val_injective twoUses).mpr
    ⟨perUse, family, fun _ _ _ => rfl⟩


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedSolutionGluing
