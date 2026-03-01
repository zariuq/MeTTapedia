import Mettapedia.OSLF.Framework.LanguageEqCategory

/-!
# LanguageEqCategoryLaws

Bundled category laws for `LanguageEqCategory`, stated over `HomEq`.
-/

namespace Mettapedia.OSLF.Framework.LanguageEqCategoryLaws

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.LanguageEqCategory

/-- Category laws bundled over `HomEq`. -/
structure EqCategoryLaws where
  left_id :
    ∀ {L₁ L₂ : Obj} (f : Hom L₁ L₂),
      HomEq (comp (id L₁) f) f
  right_id :
    ∀ {L₁ L₂ : Obj} (f : Hom L₁ L₂),
      HomEq (comp f (id L₂)) f
  assoc :
    ∀ {L₁ L₂ L₃ L₄ : Obj}
      (f : Hom L₁ L₂) (g : Hom L₂ L₃) (h : Hom L₃ L₄),
      HomEq (comp (comp f g) h) (comp f (comp g h))
  mapPred_id :
    ∀ (L : Obj) (ψ : Pattern → Prop),
      mapPred (id L) ψ = ψ
  mapPred_comp :
    ∀ {L₁ L₂ L₃ : Obj}
      (f : Hom L₁ L₂) (g : Hom L₂ L₃)
      (ψ : Pattern → Prop),
      mapPred (comp f g) ψ = mapPred f (mapPred g ψ)

/-- Canonical bundled laws for `LanguageEqCategory`. -/
theorem languageEqCategoryLaws : EqCategoryLaws where
  left_id := by
    intro L₁ L₂ f
    exact comp_id_left f
  right_id := by
    intro L₁ L₂ f
    exact comp_id_right f
  assoc := by
    intro L₁ L₂ L₃ L₄ f g h
    exact comp_assoc f g h
  mapPred_id := by
    intro L ψ
    exact mapPred_id L ψ
  mapPred_comp := by
    intro L₁ L₂ L₃ f g ψ
    exact mapPred_comp f g ψ

/-- Access theorem: left identity. -/
theorem left_id_holds
    {L₁ L₂ : Obj} (f : Hom L₁ L₂) :
    HomEq (comp (id L₁) f) f :=
  languageEqCategoryLaws.left_id f

/-- Access theorem: right identity. -/
theorem right_id_holds
    {L₁ L₂ : Obj} (f : Hom L₁ L₂) :
    HomEq (comp f (id L₂)) f :=
  languageEqCategoryLaws.right_id f

/-- Access theorem: associativity. -/
theorem assoc_holds
    {L₁ L₂ L₃ L₄ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) (h : Hom L₃ L₄) :
    HomEq (comp (comp f g) h) (comp f (comp g h)) :=
  languageEqCategoryLaws.assoc f g h

/-- Access theorem: identity law for predicate pullback. -/
theorem mapPred_id_holds
    (L : Obj) (ψ : Pattern → Prop) :
    mapPred (id L) ψ = ψ :=
  languageEqCategoryLaws.mapPred_id L ψ

/-- Access theorem: composition law for predicate pullback. -/
theorem mapPred_comp_holds
    {L₁ L₂ L₃ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop) :
    mapPred (comp f g) ψ = mapPred f (mapPred g ψ) :=
  languageEqCategoryLaws.mapPred_comp f g ψ

end Mettapedia.OSLF.Framework.LanguageEqCategoryLaws
