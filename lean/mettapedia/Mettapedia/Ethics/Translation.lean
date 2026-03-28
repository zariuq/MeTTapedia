import Mettapedia.Ethics.Theory

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u v w

/-- A translation relation from `S₁` to `S₂`. -/
abbrev TranslationRel (S₁ : Type u) (S₂ : Type v) : Type (max u v) :=
  S₁ → S₂ → Prop

/-- Prop-level existence of some translation target. -/
def Translates {S₁ : Type u} {S₂ : Type v}
    (R : TranslationRel S₁ S₂) (s : S₁) : Prop :=
  ∃ t, R s t

/-- Witness-carrying existence of a translation target. -/
abbrev Witnessed {S₁ : Type u} {S₂ : Type v}
    (R : TranslationRel S₁ S₂) (s : S₁) :=
  PSigma fun t : S₂ => R s t

theorem witnessed_to_translates {S₁ : Type u} {S₂ : Type v}
    {R : TranslationRel S₁ S₂} {s : S₁} :
    Witnessed R s → Translates R s := by
  intro h
  exact ⟨h.fst, h.snd⟩

end Mettapedia.Ethics
