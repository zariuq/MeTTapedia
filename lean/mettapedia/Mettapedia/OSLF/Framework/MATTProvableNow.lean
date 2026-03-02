import Mettapedia.OSLF.Framework.LanguageEqCategory
import Mettapedia.OSLF.Framework.LanguageEqCategoryLaws
import Mettapedia.OSLF.Framework.Mode2Skeleton
import Mettapedia.OSLF.Framework.Mode2PureBoundary
import Mettapedia.OSLF.Framework.ModeMapPredCommutingSquares

/-!
# MATTProvableNow

Conservative theorem bundle for currently proved MATT-style structure in the
MeTTa-IL OSLF framework.
-/

namespace Mettapedia.OSLF.Framework.MATTProvableNow

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.ModeTheory
open Mettapedia.OSLF.Framework.LanguageEqCategory
open Mettapedia.OSLF.Framework.LanguageEqCategoryLaws
open Mettapedia.OSLF.Framework.Mode2Skeleton
open Mettapedia.OSLF.Framework.Mode2PureBoundary
open Mettapedia.OSLF.Framework.ModeMapPredCommutingSquares
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-- The doctrine's Galois field is definitionally the framework one. -/
@[simp] theorem doctrine_galois_is_langGalois (L : LanguageDef) :
    mettaILRuntimeBehavioralDoctrine.galois L = langGalois L :=
  doctrine_galois_eq L

/-- The doctrine's modal adjunction field is definitionally the framework one. -/
@[simp] theorem doctrine_adjunction_is_langModalAdjunction (L : LanguageDef) :
    mettaILRuntimeBehavioralDoctrine.modalAdjunction L =
      Mettapedia.OSLF.Framework.CategoryBridge.langModalAdjunction L :=
  doctrine_modalAdjunction_eq L

/-- Category-wrapper predicate transport is functorial under composition. -/
theorem eqCategory_mapPred_functorial
    {L₁ L₂ L₃ : LanguageDef}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) :
    mapPred (comp f g) = (mapPred f) ∘ (mapPred g) :=
  mapPred_comp_fn f g

/-- Runtime edges in mode skeleton agree with category-wrapper predicate pullback. -/
@[simp] theorem runtime_mode_mapPred_agrees
    {L₁ L₂ : LanguageDef}
    (f : Hom L₁ L₂) (ψ : Pattern → Prop) :
    Mode2Skeleton.ModeHom.mapPred (Mode2Skeleton.ModeHom.runtimeMap f) ψ =
      mapPred f ψ := rfl

/-- Runtime edges in mode skeleton agree with category-wrapper term maps. -/
@[simp] theorem runtime_mode_termMap_agrees
    {L₁ L₂ : LanguageDef}
    (f : Hom L₁ L₂) (p : Pattern) :
    (Mode2Skeleton.ModeHom.runtimeMap f).termMap p = f.mapTerm p := rfl

/-- Coherence: runtime-mode composition agrees with category-wrapper pullback composition. -/
theorem runtime_mode_comp_coherence
    {L₁ L₂ L₃ : LanguageDef}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) (ψ : Pattern → Prop) :
    Mode2Skeleton.ModeHom.mapPred
      (Mode2Skeleton.ModeHom.comp
        (Mode2Skeleton.ModeHom.runtimeMap f)
        (Mode2Skeleton.ModeHom.runtimeMap g)) ψ =
      mapPred (comp f g) ψ := by
  simp [Mode2Skeleton.ModeHom.comp, LanguageEqCategory.comp, mapPred]

/-- Eq-category law bundle agrees with direct functorial pullback statement. -/
theorem eqCategory_law_bundle_agrees
    {L₁ L₂ L₃ : LanguageDef}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) (ψ : Pattern → Prop) :
    mapPred (comp f g) ψ = mapPred f (mapPred g ψ) := by
  exact mapPred_comp_holds f g ψ

/-- Mode-level and category-level runtime/runtime commuting square. -/
theorem runtime_runtime_square_coherence
    {L₁ L₂ L₃ : LanguageDef}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) (ψ : Pattern → Prop) :
    ModeHom.mapPred (ModeHom.runtimeMap (comp f g)) ψ =
      mapPred (comp f g) ψ := by
  exact runtime_runtime_square f g ψ

/-- Mode-level and category-level runtime/behavioral commuting square. -/
theorem runtime_behavioral_square_coherence
    {L₁ L₂ L₃ : LanguageDef}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃) (ψ : Pattern → Prop) :
    ModeHom.mapPred (ModeHom.runtimeToBehavioral (comp f g)) ψ =
      mapPred (comp f g) ψ := by
  exact runtime_behavioral_square f g ψ

/-- Runtime-map diamond witness transport along Eq-language morphisms. -/
theorem runtime_mode_diamond_transport
    {L₁ L₂ : LanguageDef}
    (f : Hom L₁ L₂)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    ∃ q, langReduces L₁ p q ∧ φ q ∧
      ∃ T, LangReducesStar L₂ (f.mapTerm p) T ∧ T = f.mapTerm q := by
  exact diamond_witness_transport (m := f) (φ := φ) (p := p) h

/-- Runtime-map diamond witness transport under composition. -/
theorem runtime_mode_diamond_transport_comp
    {L₁ L₂ L₃ : LanguageDef}
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    ∃ q, langReduces L₁ p q ∧ φ q ∧
      ∃ T, LangReducesStar L₃ ((comp f g).mapTerm p) T ∧ T = (comp f g).mapTerm q := by
  exact diamond_witness_transport_comp (m₁₂ := f) (m₂₃ := g) (φ := φ) (p := p) h

/-- Bundled "provable-now" MATT claims (no full 2-category overclaim). -/
theorem matt_provable_now_bundle
    {L₁ L₂ L₃ : LanguageDef}
    (L : LanguageDef)
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop) :
    mettaILRuntimeBehavioralDoctrine.galois L = langGalois L ∧
    mettaILRuntimeBehavioralDoctrine.modalAdjunction L =
      Mettapedia.OSLF.Framework.CategoryBridge.langModalAdjunction L ∧
    mapPred (comp f g) ψ = mapPred f (mapPred g ψ) ∧
    Mode2Skeleton.ModeHom.mapPred
      (Mode2Skeleton.ModeHom.comp
        (Mode2Skeleton.ModeHom.runtimeMap f)
        (Mode2Skeleton.ModeHom.runtimeMap g)) ψ =
      Mode2Skeleton.ModeHom.mapPred
        (Mode2Skeleton.ModeHom.runtimeMap f)
        (Mode2Skeleton.ModeHom.mapPred
          (Mode2Skeleton.ModeHom.runtimeMap g) ψ) := by
  refine ⟨doctrine_galois_eq L, doctrine_modalAdjunction_eq L, ?_, ?_⟩
  · exact mapPred_comp f g ψ
  · exact Mode2Skeleton.ModeHom.mapPred_comp
      (Mode2Skeleton.ModeHom.runtimeMap f)
      (Mode2Skeleton.ModeHom.runtimeMap g)
      ψ

/-- Extended conservative bundle including theorem-level commuting-square claims. -/
theorem matt_provable_now_bundle_ext
    {L₁ L₂ L₃ : LanguageDef}
    (L : LanguageDef)
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop) :
    mettaILRuntimeBehavioralDoctrine.galois L = langGalois L ∧
    mettaILRuntimeBehavioralDoctrine.modalAdjunction L =
      Mettapedia.OSLF.Framework.CategoryBridge.langModalAdjunction L ∧
    mapPred (comp f g) ψ = mapPred f (mapPred g ψ) ∧
    ModeHom.mapPred (ModeHom.runtimeMap (comp f g)) ψ =
      mapPred (comp f g) ψ ∧
    ModeHom.mapPred (ModeHom.runtimeToBehavioral (comp f g)) ψ =
      mapPred (comp f g) ψ := by
  refine ⟨doctrine_galois_eq L, doctrine_modalAdjunction_eq L, ?_, ?_, ?_⟩
  · exact mapPred_comp_holds f g ψ
  · exact runtime_runtime_square f g ψ
  · exact runtime_behavioral_square f g ψ

/-- Extended bundle with transport witness on runtime maps. -/
theorem matt_provable_now_bundle_transport
    {L₁ L₂ L₃ : LanguageDef}
    (L : LanguageDef)
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    mettaILRuntimeBehavioralDoctrine.galois L = langGalois L ∧
    mapPred (comp f g) ψ = mapPred f (mapPred g ψ) ∧
    (∃ q, langReduces L₁ p q ∧ φ q ∧
      ∃ T, LangReducesStar L₃ ((comp f g).mapTerm p) T ∧
        T = (comp f g).mapTerm q) := by
  refine ⟨doctrine_galois_eq L, mapPred_comp_holds f g ψ, ?_⟩
  exact runtime_mode_diamond_transport_comp f g h

/-- Pure object is isolated in the current mode skeleton. -/
theorem pure_mode_isolation
    {X Y : ModeObj} (f : ModeHom X Y) :
    X = .pure ∨ Y = .pure →
    X = .pure ∧ Y = .pure ∧ HEq f (ModeHom.id (X := .pure)) :=
  pure_boundary_characterization f

/-- Specialization: canonical runtime→behavioral witness transport for
`mettaPure` in the current mode skeleton. -/
theorem mettaPure_runtime_behavioral_transport
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond Mettapedia.Languages.MeTTa.Pure.Core.mettaPure φ p) :
    ∃ q, langReduces Mettapedia.Languages.MeTTa.Pure.Core.mettaPure p q ∧ φ q ∧
      ∃ T, LangReducesStar Mettapedia.Languages.MeTTa.Pure.Core.mettaPure
        (mettaPureRuntimeToBehavioral.termMap p) T ∧
        T = mettaPureRuntimeToBehavioral.termMap q :=
  mettaPure_runtime_behavioral_diamond_transport h

end Mettapedia.OSLF.Framework.MATTProvableNow
