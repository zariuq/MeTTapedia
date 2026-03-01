import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.LanguageMorphism

/-!
# Mode-Theoretic Packaging for MeTTa-IL OSLF

This file packages existing framework theorems into an explicit
runtime/behavioral indexed-modal interface.

It intentionally states only what is already proven in the codebase:
- per-language modal operators `langDiamond` and `langBox`
- per-language Galois connection `langGalois`
- categorical lift `langModalAdjunction`
- presheaf-primary fiber agreement `langOSLFFibrationUsing_presheafAgreement`
- morphism-level diamond preservation `LanguageMorphism.preserves_diamond`

This is the strongest current foundation for an "MTT/MaTT-style" claim
without over-claiming a full mode-2-category theorem.
-/

namespace Mettapedia.OSLF.Framework.ModeTheory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.LangMorphism

/-- Runtime/behavioral indexed doctrine induced by `LanguageDef`. -/
structure RuntimeBehavioralIndexedDoctrine where
  /-- Runtime transition modality. -/
  Diamond : LanguageDef → (Pattern → Prop) → (Pattern → Prop)
  /-- Runtime predecessor modality. -/
  Box : LanguageDef → (Pattern → Prop) → (Pattern → Prop)
  /-- Per-language modal Galois connection. -/
  galois : ∀ lang, GaloisConnection (Diamond lang) (Box lang)
  /-- Per-language categorical adjunction induced from `galois`. -/
  modalAdjunction :
    ∀ lang,
      ((langGaloisL lang).monotone_l.functor ⊣
        (langGaloisL lang).monotone_u.functor)
  /-- Generated OSLF system for each runtime language wrapper. -/
  oslf : ∀ lang (procSort : String), OSLFTypeSystem (langRewriteSystem lang procSort)
  /-- Sort-indexed behavioral fiber family. -/
  fiberFamily : ∀ (_lang : LanguageDef) (_procSort : String), String → Type

/-- Canonical doctrine instance from existing OSLF synthesis. -/
noncomputable def mettaILRuntimeBehavioralDoctrine : RuntimeBehavioralIndexedDoctrine where
  Diamond := langDiamond
  Box := langBox
  galois := langGalois
  modalAdjunction := langModalAdjunction
  oslf := fun lang procSort => langOSLF lang procSort
  fiberFamily := fun lang procSort => langOSLFFiberFamily lang procSort

/-- The doctrine recovers the framework's per-language modal adjunction. -/
@[simp] theorem doctrine_modalAdjunction_eq (lang : LanguageDef) :
    mettaILRuntimeBehavioralDoctrine.modalAdjunction lang = langModalAdjunction lang := rfl

/-- The doctrine recovers the framework's per-language modal Galois connection. -/
@[simp] theorem doctrine_galois_eq (lang : LanguageDef) :
    mettaILRuntimeBehavioralDoctrine.galois lang = langGalois lang := rfl

/-- Presheaf-primary and wrapper-fiber views coincide for any language wrapper. -/
noncomputable def doctrine_fiberAgreement (lang : LanguageDef) (procSort : String := "Proc") :
    (predFibrationPresheafPrimary
      (C := CategoryTheory.Discrete String)
      (instC := inferInstance)).Sub
      (sortFamilyPresheaf (langRewriteSystem lang procSort)
        (fun s => (langRewriteSystem lang procSort).Term s))
      ≃
    (∀ s : String,
      mettaILRuntimeBehavioralDoctrine.fiberFamily lang procSort s) := by
  simpa [mettaILRuntimeBehavioralDoctrine] using
    (langOSLFFibrationUsing_presheafAgreement (lang := lang) (procSort := procSort))

/-- Morphisms preserve the doctrine's diamond modality (forward direction). -/
theorem doctrine_morphism_preserves_diamond
    {L₁ L₂ : LanguageDef} {sc : Pattern → Pattern → Prop}
    (m : LanguageMorphism L₁ L₂ sc)
    {φ : Pattern → Prop} {p : Pattern}
    (h : mettaILRuntimeBehavioralDoctrine.Diamond L₁ φ p) :
    ∃ q, langReduces L₁ p q ∧ φ q ∧
      ∃ T, LangReducesStar L₂ (m.mapTerm p) T ∧ sc T (m.mapTerm q) := by
  simpa [mettaILRuntimeBehavioralDoctrine] using
    (LanguageMorphism.preserves_diamond (m := m) (φ := φ) (p := p) h)

end Mettapedia.OSLF.Framework.ModeTheory
