import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Denotation

/-!
# Related substitutions

Related substitutions send each variable to related terms of its substituted
type. They follow world morphisms and extend by a related pair. In a valid
context they form a partial equivalence, because the type of each variable
has one denotation under related substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

theorem EqSubst.cons {n m : Nat} {Γ : Ctx Head n} {ξ : World M.reading m} {σ σ' : Sub Head n m}
    (eq : EqSubst M Γ ξ σ σ') {A : Tm Head n} {R : Rel Head m}
    (den : Den M ξ (Presentation.subst σ A) R) {a a' : Tm Head m} (h : R a a') :
    EqSubst M (.snoc Γ A) ξ (consSub a σ) (consSub a' σ') :=
  ⟨eq, R, den, h⟩

theorem EqSubst.lookup : ∀ {n m : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m}, EqSubst M Γ ξ σ σ' → ∀ i : Fin n,
      ∃ R, Den M ξ (Presentation.subst σ (Ctx.lookup Γ i)) R ∧ R (σ i) (σ' i)
  | _, _, .nil, _, _, _, _, i => nomatch i
  | _, _, .snoc Γ A, _, σ, _, eq, i => by
      obtain ⟨tail, R, den, h⟩ := eq
      refine Fin.cases ?_ (fun j => ?_) i
      · refine ⟨R, ?_, h⟩
        simp only [Ctx.lookup, Fin.cases_zero]
        rw [subst_rename_wk]
        exact den
      · obtain ⟨R', den', h'⟩ := EqSubst.lookup tail j
        refine ⟨R', ?_, h'⟩
        simp only [Ctx.lookup, Fin.cases_succ]
        rw [subst_rename_wk]
        exact den'

section Laws

variable (laws : M.Laws)
include laws

theorem EqSubst.rename : ∀ {n m : Nat} {Γ : Ctx Head n} {ξ : World M.reading m}
    {σ σ' : Sub Head n m}, EqSubst M Γ ξ σ σ' →
      ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k}, Morph ξ ξ' ρ →
        EqSubst M Γ ξ' (fun i => Presentation.rename ρ (σ i))
          (fun i => Presentation.rename ρ (σ' i))
  | _, _, .nil, _, _, _, _, _, _, _, _ => trivial
  | _, _, .snoc Γ A, _, σ, _, eq, _, _, ρ, w => by
      obtain ⟨tail, R, den, h⟩ := eq
      obtain ⟨R', den', map⟩ := den.rename laws w
      refine ⟨EqSubst.rename tail w, R', ?_, map h⟩
      rw [rename_subst] at den'
      exact den'

theorem EqSubst.symm : ∀ {n m : Nat} {Γ : Ctx Head n}, ValidCtx M Γ → ∀ {ξ : World M.reading m}
    {σ σ' : Sub Head n m}, EqSubst M Γ ξ σ σ' → EqSubst M Γ ξ σ' σ
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .snoc Γ A, valid, _, _, _, eq => by
      obtain ⟨validΓ, validA⟩ := valid
      obtain ⟨tail, R, den, h⟩ := eq
      obtain ⟨R', den₁, den₂⟩ := validA tail
      rw [Den.deterministic laws den den₁] at h
      exact ⟨EqSubst.symm validΓ tail, R', den₂, den₁.symm laws h⟩

theorem EqSubst.trans : ∀ {n m : Nat} {Γ : Ctx Head n}, ValidCtx M Γ → ∀ {ξ : World M.reading m}
    {σ σ' σ'' : Sub Head n m}, EqSubst M Γ ξ σ σ' → EqSubst M Γ ξ σ' σ'' →
      EqSubst M Γ ξ σ σ''
  | _, _, .nil, _, _, _, _, _, _, _ => trivial
  | _, _, .snoc Γ A, valid, _, _, _, _, eq, eq' => by
      obtain ⟨validΓ, validA⟩ := valid
      obtain ⟨tail, R, den, h⟩ := eq
      obtain ⟨tail', R', den', h'⟩ := eq'
      obtain ⟨S, denS, denS'⟩ := validA tail
      rw [Den.deterministic laws den denS] at h
      rw [Den.deterministic laws den' denS'] at h'
      exact ⟨EqSubst.trans validΓ tail tail', S, denS, denS.trans laws h h'⟩

theorem EqSubst.refl_left {n m : Nat} {Γ : Ctx Head n} (valid : ValidCtx M Γ) {ξ : World M.reading m}
    {σ σ' : Sub Head n m} (eq : EqSubst M Γ ξ σ σ') : EqSubst M Γ ξ σ σ :=
  EqSubst.trans laws valid eq (EqSubst.symm laws valid eq)

theorem EqSubst.refl_right {n m : Nat} {Γ : Ctx Head n} (valid : ValidCtx M Γ) {ξ : World M.reading m}
    {σ σ' : Sub Head n m} (eq : EqSubst M Γ ξ σ σ') : EqSubst M Γ ξ σ' σ' :=
  EqSubst.trans laws valid (EqSubst.symm laws valid eq) eq

end Laws

/-! ## Valid types have one denotation -/

theorem ValidTy.den {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (valid : ValidTy M Γ A)
    {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} (eq : EqSubst M Γ ξ σ σ') :
    ∃ R, Den M ξ (Presentation.subst σ A) R :=
  let ⟨R, den, _⟩ := valid eq
  ⟨R, den⟩

theorem ValidTy.den_right (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    (valid : ValidTy M Γ A) {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
    (eq : EqSubst M Γ ξ σ σ') {R : Rel Head m} (den : Den M ξ (Presentation.subst σ A) R) :
    Den M ξ (Presentation.subst σ' A) R := by
  obtain ⟨R', den₁, den₂⟩ := valid eq
  rw [Den.deterministic laws den den₁]
  exact den₂

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
