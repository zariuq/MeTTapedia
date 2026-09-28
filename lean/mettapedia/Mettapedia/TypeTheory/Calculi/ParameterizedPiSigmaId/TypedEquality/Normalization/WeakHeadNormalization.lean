import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Injectivity

/-!
# Weak-head normalization

Every reducible type and every reducible term reduces to a weak-head normal
form: each case of the relation records the reduction to the normal form, and
the normal forms it admits (universes, neutral terms, heads, functions, pairs,
reflexivity, constructor forms) do not reduce. By the fundamental lemma, every
typed term and every type of a formed context is weakly head normalizing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- A reducible type reduces to a weak-head normal form. -/
theorem LR.type_whnf {l : L} {rec : L → RedRel Head} {n : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} {P : Pack Head n} (reducible : LR S l rec Γ A P) :
    ∃ B, WhRed S.R S.roles A B ∧ Whnf S.R S.roles B := by
  cases reducible with
  | sort _ _ _ red => exact ⟨_, red.red, head_whnf S.shape _⟩
  | neutral red neutral => exact ⟨_, red.red, neutral.whnf S.shape⟩
  | ground _ red => exact ⟨_, red.red, head_whnf S.shape _⟩
  | pi red => exact ⟨_, red.red, pi_whnf S.shape _ _⟩
  | sigma red => exact ⟨_, red.red, sigma_whnf S.shape _ _⟩
  | ident red => exact ⟨_, red.red, id_whnf S.shape _ _ _⟩
  | inductiveType red role => exact ⟨_, red.red, inductive_whnf S.shape role⟩

/-- A reducible term reduces to a weak-head normal form. -/
theorem LR.redTm_whnf {l : L} {rec : L → RedRel Head} {n : Nat} {Γ : Ctx Head n}
    {A : Tm Head n} {P : Pack Head n} (reducible : LR S l rec Γ A P) {t : Tm Head n}
    (ht : P.redTm t) : ∃ nf, WhRed S.R S.roles t nf ∧ Whnf S.R S.roles nf := by
  cases reducible with
  | sort =>
      obtain ⟨nf, red, form, _⟩ := ht
      exact ⟨nf, red.red, form.whnf⟩
  | neutral =>
      obtain ⟨nf, red, neutral, _⟩ := ht
      exact ⟨nf, red.red, neutral.whnf S.shape⟩
  | ground =>
      obtain ⟨nf, red, neutral, _⟩ := ht
      exact ⟨nf, red.red, neutral.whnf S.shape⟩
  | pi =>
      obtain ⟨nf, red, isFun, _⟩ := ht
      exact ⟨nf, red.red, isFun.whnf⟩
  | sigma =>
      obtain ⟨nf, red, isPair, _⟩ := ht
      exact ⟨nf, red.red, isPair.whnf⟩
  | ident =>
      obtain ⟨nf, red, _, prop⟩ := ht
      exact ⟨nf, red.red, prop.whnf⟩
  | inductiveType _ role =>
      obtain ⟨red, _, normal⟩ := ht
      exact ⟨_, red.red, normal.whnf role⟩

theorem Reducible.type_whnf {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) : ∃ B, WhRed S.R S.roles A B ∧ Whnf S.R S.roles B := by
  obtain ⟨l, r⟩ := reducible
  exact LR.type_whnf r

theorem Reducible.redTm_whnf {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Γ A P) {t : Tm Head n} (ht : P.redTm t) :
    ∃ nf, WhRed S.R S.roles t nf ∧ Whnf S.R S.roles nf := by
  obtain ⟨l, r⟩ := reducible
  exact LR.redTm_whnf r ht

section Normalization

variable (laws : S.E.Laws S.R S.roles) (constants : SemanticConstants S)
include laws constants

/-- Every typed term of a formed context is weakly head normalizing. -/
theorem Typed.whnf_exists {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typing : Typed S.R Γ t A) (formed : CtxFormed S.R Γ) :
    ∃ nf, WhRed S.R S.roles t nf ∧ Whnf S.R S.roles nf := by
  obtain ⟨r, h⟩ := Typed.reducible laws constants typing formed
  exact r.redTm_whnf h

/-- Every type of a formed context is weakly head normalizing. -/
theorem IsType.whnf_exists {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    (formed' : IsType S.R Γ A) (formed : CtxFormed S.R Γ) :
    ∃ B, WhRed S.R S.roles A B ∧ Whnf S.R S.roles B :=
  (IsType.reducible laws constants formed' formed).type_whnf

end Normalization

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
