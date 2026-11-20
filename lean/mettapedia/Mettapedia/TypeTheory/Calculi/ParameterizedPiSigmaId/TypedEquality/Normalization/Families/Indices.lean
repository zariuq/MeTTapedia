import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Declaration

/-!
# Index agreement at simple inductive index types

Which constructors of a family can sit at an index is decided by reducible equality at the
index type. When the index type is a simple inductive type, that equality is rigid on
constructors: a constructor is reducibly equal only to the same constructor with reducibly
equal arguments (`ctorEq_inv`), and never to a variable (`not_varEq_ctor`). So at a closed
index the constructors of a family whose target is another closed index are excluded, and at
a variable index every constructor whose target is a closed index is excluded.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace Families

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- A weak-head normal form reduces only to itself. -/
theorem whnf_reduct_eq {n : Nat} {t u : Tm Head n} (normal : Whnf S.R S.roles t)
    (red : WhRed S.R S.roles t u) : u = t := by
  cases red using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ => exact absurd step (normal _)

section Simple

variable {n : Nat} {Γ : Ctx Head n} {T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {fieldPack : Tm Head 0 → Pack Head n}

/-- A spine of a declared constructor is a weak-head normal form and not neutral. -/
theorem ctorSpine_rigid {k : DeclName} {arity : Nat} (role : S.roles k = .constructor arity)
    (args : List (Tm Head n)) :
    Whnf S.R S.roles (appSpine (.const k) args) ∧ ¬ Neutral S.roles (appSpine (.const k) args) :=
  ⟨canonical_whnf S.shape (.inr ⟨_, _, _, role, rfl⟩),
    fun nNf => nNf.not_canonical (.inr ⟨_, _, _, role, rfl⟩)⟩

/-- Reducibly equal normal forms that are constructor spines are the same listed constructor
with reducibly equal arguments. -/
theorem ctorEqNf_inv {k k' : DeclName} {arity : Nat} (role : S.roles k = .constructor arity)
    {args args' : List (Tm Head n)} {nf nf' : Tm Head n}
    (normal : IndEqNf S Γ T ctors fieldPack nf nf') (hnf : nf = appSpine (.const k) args)
    (hnf' : nf' = appSpine (.const k') args') :
    k = k' ∧ ∃ fields, (k, fields) ∈ ctors ∧ IndEqFields S Γ T ctors fieldPack fields args args' := by
  cases normal with
  | ctor mem fields =>
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective hnf
      obtain ⟨rfl, rfl⟩ := appSpine_const_injective hnf'
      exact ⟨rfl, _, mem, fields⟩
  | neutral nNf _ _ =>
      subst hnf
      exact absurd nNf (ctorSpine_rigid role args).2

/-- Reducibly equal constructor spines at a simple inductive type are the same listed
constructor with reducibly equal arguments. -/
theorem ctorEq_inv {k k' : DeclName} {arity arity' : Nat} (role : S.roles k = .constructor arity)
    (role' : S.roles k' = .constructor arity') {args args' : List (Tm Head n)}
    (equal : IndEqTm S Γ T ctors fieldPack (appSpine (.const k) args)
      (appSpine (.const k') args')) :
    k = k' ∧ ∃ fields, (k, fields) ∈ ctors ∧ IndEqFields S Γ T ctors fieldPack fields args args' := by
  obtain ⟨red, red', _, normal⟩ := equal
  have e := whnf_reduct_eq (ctorSpine_rigid role args).1 red.red
  have e' := whnf_reduct_eq (ctorSpine_rigid role' args').1 red'.red
  exact ctorEqNf_inv role normal e e'

/-- Two different constructors are not reducibly equal. -/
theorem not_ctorEq_ctor {k k' : DeclName} {arity arity' : Nat}
    (role : S.roles k = .constructor arity) (role' : S.roles k' = .constructor arity')
    (different : k ≠ k') {args args' : List (Tm Head n)} :
    ¬ IndEqTm S Γ T ctors fieldPack (appSpine (.const k) args) (appSpine (.const k') args') :=
  fun equal => different (ctorEq_inv role role' equal).1

/-- A variable is not reducibly equal to a constructor spine. -/
theorem not_varEq_ctor {k : DeclName} {arity : Nat} (role : S.roles k = .constructor arity)
    (i : Fin n) {args : List (Tm Head n)} :
    ¬ IndEqTm S Γ T ctors fieldPack (.var i) (appSpine (.const k) args) := by
  rintro ⟨red, red', _, normal⟩
  have e := whnf_reduct_eq (var_whnf S.shape i) red.red
  have e' := whnf_reduct_eq (ctorSpine_rigid role args).1 red'.red
  subst e e'
  generalize hnf : (Tm.var i : Tm Head n) = nf at normal
  generalize hnf' : appSpine (.const k) args = nf' at normal
  cases normal with
  | ctor _ _ => exact appSpine_const_ne_var hnf.symm
  | neutral _ nNf' _ =>
      subst hnf'
      exact (ctorSpine_rigid role args).2 nNf'

/-- A constructor spine is not reducibly equal to a variable. -/
theorem not_ctorEq_var {k : DeclName} {arity : Nat} (role : S.roles k = .constructor arity)
    (i : Fin n) {args : List (Tm Head n)} :
    ¬ IndEqTm S Γ T ctors fieldPack (appSpine (.const k) args) (.var i) := by
  rintro ⟨red, red', _, normal⟩
  have e := whnf_reduct_eq (ctorSpine_rigid role args).1 red.red
  have e' := whnf_reduct_eq (var_whnf S.shape i) red'.red
  subst e e'
  generalize hnf : appSpine (.const k) args = nf at normal
  generalize hnf' : (Tm.var i : Tm Head n) = nf' at normal
  cases normal with
  | ctor _ _ => exact appSpine_const_ne_var hnf'.symm
  | neutral nNf _ _ =>
      subst hnf
      exact (ctorSpine_rigid role args).2 nNf

end Simple

end Families
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
