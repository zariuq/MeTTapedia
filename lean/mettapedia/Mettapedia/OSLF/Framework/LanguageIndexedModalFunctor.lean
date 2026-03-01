import Mettapedia.OSLF.Framework.ModeTheory

/-!
# Language-Indexed Modal Functor (Eq Morphism Core)

This module packages the currently-proven functorial transport layer over
`LanguageMorphism _ _ Eq`:

- predicate pullback along language morphisms,
- identity/composition laws,
- modal witness transport via `preserves_diamond`.

It is intentionally conservative: no over-claim of a full 2-category model.
-/

namespace Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism

abbrev LanguageEqHom (L₁ L₂ : LanguageDef) := LanguageMorphism L₁ L₂ Eq

/-- Predicate pullback along a language morphism. -/
def predPullback {L₁ L₂ : LanguageDef}
    (m : LanguageEqHom L₁ L₂) :
    (Pattern → Prop) → (Pattern → Prop) :=
  fun ψ p => ψ (m.mapTerm p)

@[simp] theorem predPullback_id (L : LanguageDef) (ψ : Pattern → Prop) :
    predPullback (idLanguageMorphism L) ψ = ψ := by
  funext p
  rfl

@[simp] theorem predPullback_comp
    {L₁ L₂ L₃ : LanguageDef}
    (m₁₂ : LanguageEqHom L₁ L₂)
    (m₂₃ : LanguageEqHom L₂ L₃)
    (ψ : Pattern → Prop) :
    predPullback (composeLanguageMorphism m₁₂ m₂₃) ψ =
      predPullback m₁₂ (predPullback m₂₃ ψ) := by
  funext p
  rfl

/-- Minimal functor package for language-indexed predicate transport. -/
structure IndexedPredFunctor where
  mapHom : ∀ {L₁ L₂ : LanguageDef}, LanguageEqHom L₁ L₂ →
    ((Pattern → Prop) → (Pattern → Prop))
  map_id : ∀ (L : LanguageDef) (ψ : Pattern → Prop),
    mapHom (idLanguageMorphism L) ψ = ψ
  map_comp :
    ∀ {L₁ L₂ L₃ : LanguageDef}
      (m₁₂ : LanguageEqHom L₁ L₂)
      (m₂₃ : LanguageEqHom L₂ L₃)
      (ψ : Pattern → Prop),
      mapHom (composeLanguageMorphism m₁₂ m₂₃) ψ =
        mapHom m₁₂ (mapHom m₂₃ ψ)

/-- Canonical pullback functor on predicates induced by language morphisms. -/
def runtimePredicatePullbackFunctor : IndexedPredFunctor where
  mapHom := fun {_ _} m => predPullback m
  map_id := predPullback_id
  map_comp := predPullback_comp

/-- Diamond witness transport along an Eq-language morphism. -/
theorem diamond_witness_transport
    {L₁ L₂ : LanguageDef}
    (m : LanguageEqHom L₁ L₂)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    ∃ q, langReduces L₁ p q ∧ φ q ∧
      ∃ T, LangReducesStar L₂ (m.mapTerm p) T ∧ T = m.mapTerm q := by
  simpa using
    (LanguageMorphism.preserves_diamond (m := m) (φ := φ) (p := p) h)

/-- Composition-level form of diamond witness transport. -/
theorem diamond_witness_transport_comp
    {L₁ L₂ L₃ : LanguageDef}
    (m₁₂ : LanguageEqHom L₁ L₂)
    (m₂₃ : LanguageEqHom L₂ L₃)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    ∃ q, langReduces L₁ p q ∧ φ q ∧
      ∃ T, LangReducesStar L₃
        ((composeLanguageMorphism m₁₂ m₂₃).mapTerm p) T ∧
        T = (composeLanguageMorphism m₁₂ m₂₃).mapTerm q := by
  simpa using
    (LanguageMorphism.preserves_diamond
      (m := composeLanguageMorphism m₁₂ m₂₃)
      (φ := φ) (p := p) h)

end Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
