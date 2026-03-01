import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-!
# Mode-2 Skeleton (Current-Proof Envelope)

A conservative mode skeleton with explicit objects and currently provable
morphisms. This is not yet a full 2-category formalization; it is the
maximal sound scaffold before MeTTa-Pure is introduced.
-/

namespace Mettapedia.OSLF.Framework.Mode2Skeleton

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-- Mode objects currently represented in the framework. -/
inductive ModeObj where
  | pure
  | runtime (lang : LanguageDef)
  | behavioral (lang : LanguageDef)

/-- Currently provable mode morphisms. -/
inductive ModeHom : ModeObj → ModeObj → Type where
  | id : ModeHom X X
  | runtimeMap {L₁ L₂ : LanguageDef} :
      LanguageEqHom L₁ L₂ → ModeHom (.runtime L₁) (.runtime L₂)
  | behavioralMap {L₁ L₂ : LanguageDef} :
      LanguageEqHom L₁ L₂ → ModeHom (.behavioral L₁) (.behavioral L₂)
  | runtimeToBehavioral {L₁ L₂ : LanguageDef} :
      LanguageEqHom L₁ L₂ → ModeHom (.runtime L₁) (.behavioral L₂)

namespace ModeHom

/-- Composition in the current mode skeleton. -/
def comp : ModeHom X Y → ModeHom Y Z → ModeHom X Z
  | f, .id => f
  | .id, g => g
  | .runtimeMap m₁₂, .runtimeMap m₂₃ =>
      .runtimeMap (composeLanguageMorphism m₁₂ m₂₃)
  | .runtimeMap m₁₂, .runtimeToBehavioral m₂₃ =>
      .runtimeToBehavioral (composeLanguageMorphism m₁₂ m₂₃)
  | .behavioralMap m₁₂, .behavioralMap m₂₃ =>
      .behavioralMap (composeLanguageMorphism m₁₂ m₂₃)
  | .runtimeToBehavioral m₁₂, .behavioralMap m₂₃ =>
      .runtimeToBehavioral (composeLanguageMorphism m₁₂ m₂₃)

infixr:80 " ≫ " => comp

@[simp] theorem comp_id_left (f : ModeHom X Y) :
    (ModeHom.id (X := X)) ≫ f = f := by
  cases f <;> rfl

@[simp] theorem comp_id_right (f : ModeHom X Y) :
    f ≫ (ModeHom.id (X := Y)) = f := by
  cases f <;> rfl

@[simp] theorem comp_assoc
    (f : ModeHom W X) (g : ModeHom X Y) (h : ModeHom Y Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  cases f <;> cases g <;> cases h <;> rfl

/-- Extract the term-level map from a mode morphism. -/
def termMap : ModeHom X Y → Pattern → Pattern
  | .id => fun p => p
  | .runtimeMap m => m.mapTerm
  | .behavioralMap m => m.mapTerm
  | .runtimeToBehavioral m => m.mapTerm

@[simp] theorem termMap_id (X : ModeObj) (p : Pattern) :
    (ModeHom.id (X := X)).termMap p = p := rfl

@[simp] theorem termMap_runtimeMap
    {L₁ L₂ : LanguageDef} (m : LanguageEqHom L₁ L₂) (p : Pattern) :
    (ModeHom.runtimeMap m).termMap p = m.mapTerm p := rfl

@[simp] theorem termMap_behavioralMap
    {L₁ L₂ : LanguageDef} (m : LanguageEqHom L₁ L₂) (p : Pattern) :
    (ModeHom.behavioralMap m).termMap p = m.mapTerm p := rfl

@[simp] theorem termMap_runtimeToBehavioral
    {L₁ L₂ : LanguageDef} (m : LanguageEqHom L₁ L₂) (p : Pattern) :
    (ModeHom.runtimeToBehavioral m).termMap p = m.mapTerm p := rfl

/-- Predicate pullback along mode morphisms (runtime/behavioral carriers). -/
def mapPred : ModeHom X Y → (Pattern → Prop) → (Pattern → Prop)
  | .id => fun ψ => ψ
  | .runtimeMap m => predPullback m
  | .behavioralMap m => predPullback m
  | .runtimeToBehavioral m => predPullback m

@[simp] theorem mapPred_id (X : ModeObj) (ψ : Pattern → Prop) :
    mapPred (ModeHom.id (X := X)) ψ = ψ := by
  rfl

@[simp] theorem mapPred_comp
    (f : ModeHom X Y) (g : ModeHom Y Z) (ψ : Pattern → Prop) :
    mapPred (f ≫ g) ψ = mapPred f (mapPred g ψ) := by
  cases f <;> cases g <;>
    simp [ModeHom.comp, mapPred, predPullback_comp]

@[simp] theorem termMap_comp
    (f : ModeHom X Y) (g : ModeHom Y Z) (p : Pattern) :
    (f ≫ g).termMap p = g.termMap (f.termMap p) := by
  cases f <;> cases g <;>
    simp [ModeHom.comp, termMap, composeLanguageMorphism_mapTerm]

@[simp] theorem mapPred_comp_assoc
    (f : ModeHom W X) (g : ModeHom X Y) (h : ModeHom Y Z)
    (ψ : Pattern → Prop) :
    mapPred ((f ≫ g) ≫ h) ψ = mapPred (f ≫ (g ≫ h)) ψ := by
  simp [mapPred_comp]

end ModeHom

/-- Canonical runtime→behavioral edge for a fixed language. -/
def runtimeToBehavioralCanonical (L : LanguageDef) :
    ModeHom (.runtime L) (.behavioral L) :=
  .runtimeToBehavioral (idLanguageMorphism L)

/-- Runtime→behavioral edge transports diamond witnesses. -/
theorem runtimeToBehavioral_diamond_witness
    (L : LanguageDef)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L φ p) :
    ∃ q, langReduces L p q ∧ φ q ∧
      ∃ T, LangReducesStar L
        ((runtimeToBehavioralCanonical L).termMap p) T ∧
        T = (runtimeToBehavioralCanonical L).termMap q := by
  simpa [runtimeToBehavioralCanonical, ModeHom.termMap] using
    (diamond_witness_transport (m := idLanguageMorphism L) (φ := φ) (p := p) h)

/-- Behavioral mode carries the modal adjunction for every language object. -/
noncomputable def behavioralModalAdjunction (L : LanguageDef) :
    (langGaloisL L).monotone_l.functor ⊣
      (langGaloisL L).monotone_u.functor :=
  langModalAdjunction L

end Mettapedia.OSLF.Framework.Mode2Skeleton
