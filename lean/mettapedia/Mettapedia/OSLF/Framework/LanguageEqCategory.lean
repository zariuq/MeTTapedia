import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-!
# LanguageEqCategory

Conservative category-style packaging for the `Eq`-specialized language
morphisms from `LanguageMorphism`.
-/

namespace Mettapedia.OSLF.Framework.LanguageEqCategory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-- Objects in the Eq-morphism category wrapper. -/
abbrev Obj := LanguageDef

/-- Morphisms in the Eq-morphism category wrapper. -/
abbrev Hom (L₁ L₂ : Obj) := LanguageEqHom L₁ L₂

/-- Identity morphism. -/
def id (L : Obj) : Hom L L := idLanguageMorphism L

/-- Composition of morphisms. -/
def comp {L₁ L₂ L₃ : Obj} (f : Hom L₁ L₂) (g : Hom L₂ L₃) : Hom L₁ L₃ :=
  composeLanguageMorphism f g

infixr:80 " ≫ " => comp

/-- Extensional equality for morphisms (term-map equality). -/
def HomEq {L₁ L₂ : Obj} (f g : Hom L₁ L₂) : Prop :=
  ∀ p, f.mapTerm p = g.mapTerm p

@[refl] theorem HomEq.refl {L₁ L₂ : Obj} (f : Hom L₁ L₂) : HomEq f f := by
  intro p
  rfl

@[symm] theorem HomEq.symm {L₁ L₂ : Obj} {f g : Hom L₁ L₂}
    (h : HomEq f g) : HomEq g f := by
  intro p
  symm
  exact h p

@[trans] theorem HomEq.trans {L₁ L₂ : Obj} {f g h : Hom L₁ L₂}
    (hfg : HomEq f g) (hgh : HomEq g h) : HomEq f h := by
  intro p
  exact (hfg p).trans (hgh p)

@[simp] theorem id_mapTerm (L : Obj) (p : Pattern) :
    (id L).mapTerm p = p :=
  idLanguageMorphism_mapTerm L p

@[simp] theorem comp_mapTerm
    {L₁ L₂ L₃ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) (p : Pattern) :
    (f ≫ g).mapTerm p = g.mapTerm (f.mapTerm p) :=
  composeLanguageMorphism_mapTerm f g p

theorem comp_id_left {L₁ L₂ : Obj} (f : Hom L₁ L₂) :
    HomEq ((id L₁) ≫ f) f := by
  intro p
  exact composeLanguageMorphism_id_left_mapTerm f p

theorem comp_id_right {L₁ L₂ : Obj} (f : Hom L₁ L₂) :
    HomEq (f ≫ (id L₂)) f := by
  intro p
  exact composeLanguageMorphism_id_right_mapTerm f p

theorem comp_assoc
    {L₁ L₂ L₃ L₄ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) (h : Hom L₃ L₄) :
    HomEq ((f ≫ g) ≫ h) (f ≫ (g ≫ h)) := by
  intro p
  exact composeLanguageMorphism_assoc_mapTerm f g h p

/-- Predicate transport (contravariant pullback) along language morphisms. -/
def mapPred {L₁ L₂ : Obj} (f : Hom L₁ L₂) :
    (Pattern → Prop) → (Pattern → Prop) :=
  predPullback f

@[simp] theorem mapPred_id (L : Obj) (ψ : Pattern → Prop) :
    mapPred (id L) ψ = ψ :=
  predPullback_id L ψ

@[simp] theorem mapPred_comp
    {L₁ L₂ L₃ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) (ψ : Pattern → Prop) :
    mapPred (f ≫ g) ψ = mapPred f (mapPred g ψ) :=
  predPullback_comp f g ψ

/-- Functoriality of predicate transport at function-composition level. -/
theorem mapPred_comp_fn
    {L₁ L₂ L₃ : Obj}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) :
    mapPred (f ≫ g) = (mapPred f) ∘ (mapPred g) := by
  funext ψ
  exact mapPred_comp f g ψ

end Mettapedia.OSLF.Framework.LanguageEqCategory

