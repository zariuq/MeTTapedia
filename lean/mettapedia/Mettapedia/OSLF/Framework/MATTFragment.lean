import Mettapedia.OSLF.Framework.Mode2SkeletonLaws
import Mettapedia.OSLF.Framework.MATTProvableNow
import Mettapedia.OSLF.Framework.ModeMapPredCommutingSquares
import Mettapedia.OSLF.Framework.LanguageEqCategory

/-!
# MATTFragment — "MeTTa-IL is MaTT"

This file contains the formal content of the claim:

> **MeTTa-IL, via OSLF, is a 2-mode adjoint doctrine fragment.**

## What this means

A `TwoModeAdjointDocFrag` packages:
1. **A mode category** (objects: `{pure, runtime(L), behavioral(L)}`; proved laws: identity, associativity)
2. **A contravariant indexed predicate doctrine** (`ModeHom.mapPred`: functorial predicate pullback)
3. **A modal adjunction** at each behavioral mode (◇ ⊣ □, the OSLF Galois connection)
4. **Beck-Chevalley commuting squares** (mode-level pullback agrees with category-level pullback)

This is the **doctrinal / fibrational flavor** of multimodal adjoint type theory (MaTT),
specifically a Lawvere-hyperdoctrine-style indexed modal predicate logic over the base
category of `LanguageDef`s — not the syntactic MTT of Gratzer et al.

## Where MeTTa-IL sits in theory

| MeTTa layer     | Theory                                      |
|-----------------|---------------------------------------------|
| MeTTa-Pure      | DTT / CwF (pure dependent kernel)           |
| MeTTa-IL runtime| Operational type theory (PathMap/rewriting) |
| MeTTa-IL + OSLF | **2-mode indexed hyperdoctrine** (this file)|

## Explicit non-claims

This file does **NOT** claim:
- Full 2-category structure with 2-morphisms between mode morphisms (out of scope)
- Syntactic MTT modal type formers □_μ A, locks, context extension (out of scope)
- MeTTa-Pure subject reduction (separate work in SubjectReduction.lean)
- Full modalization of the pure boundary (pure is isolated, not yet modalized)

## References

- Lawvere, "Adjointness in Foundations" (1969) — hyperdoctrine semantics
- Gratzer et al., "Multimodal Dependent Type Theory" (LICS 2020) — syntactic MTT
- Birkedal & Møgelberg, "Intensional Type Theory with Worlds" (2013) — modal adjoint DTT
- Current formalization: `MATTClaimMap.lean`, `MATTProvableNow.lean`, `Mode2Skeleton.lean`
-/

namespace Mettapedia.OSLF.Framework.MATTFragment

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.LanguageEqCategory
open Mettapedia.OSLF.Framework.Mode2Skeleton
open Mettapedia.OSLF.Framework.ModeTheory
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.OSLF.Framework.MATTProvableNow
open Mettapedia.OSLF.Framework.ModeMapPredCommutingSquares

/-! ## The Structure -/

/-- A 2-mode adjoint doctrine fragment.

    Packages a mode category, a contravariant indexed predicate doctrine,
    a modal adjunction, and Beck-Chevalley commuting squares into one
    machine-checked object.

    MeTTa-IL via OSLF is an instance (`mettaIL_2modeDocFrag`).

    This is the formal content of "MeTTa-IL is MaTT" in the
    doctrinal / fibrational sense (not syntactic MTT). -/
structure TwoModeAdjointDocFrag where
  /-- Mode category: left identity -/
  modeId_left  : ∀ {X Y : ModeObj} (f : ModeHom X Y), ModeHom.id ≫ f = f
  /-- Mode category: right identity -/
  modeId_right : ∀ {X Y : ModeObj} (f : ModeHom X Y), f ≫ ModeHom.id = f
  /-- Mode category: associativity -/
  modeAssoc    : ∀ {W X Y Z : ModeObj}
                   (f : ModeHom W X) (g : ModeHom X Y) (h : ModeHom Y Z),
                   (f ≫ g) ≫ h = f ≫ (g ≫ h)
  /-- Doctrine: predicate pullback is identity on identity morphisms -/
  predId       : ∀ (X : ModeObj) (ψ : Pattern → Prop),
                   ModeHom.mapPred (ModeHom.id (X := X)) ψ = ψ
  /-- Doctrine: predicate pullback is contravariantly functorial -/
  predComp     : ∀ {X Y Z : ModeObj}
                   (f : ModeHom X Y) (g : ModeHom Y Z) (ψ : Pattern → Prop),
                   ModeHom.mapPred (f ≫ g) ψ =
                     ModeHom.mapPred f (ModeHom.mapPred g ψ)
  /-- Modal adjunction: the doctrine's Galois field agrees with the OSLF framework -/
  galoisAgrees : ∀ (L : LanguageDef),
                   mettaILRuntimeBehavioralDoctrine.galois L = langGalois L
  /-- Modal adjunction: the doctrine's adjunction agrees with the OSLF framework -/
  adjAgrees    : ∀ (L : LanguageDef),
                   mettaILRuntimeBehavioralDoctrine.modalAdjunction L =
                     Mettapedia.OSLF.Framework.CategoryBridge.langModalAdjunction L
  /-- Beck-Chevalley: runtime/runtime commuting square -/
  rtRtSquare   : ∀ {L₁ L₂ L₃ : LanguageDef}
                   (f : Hom L₁ L₂) (g : Hom L₂ L₃) (ψ : Pattern → Prop),
                   ModeHom.mapPred (ModeHom.runtimeMap (comp f g)) ψ =
                     mapPred (comp f g) ψ
  /-- Beck-Chevalley: runtime/behavioral commuting square -/
  rtBehSquare  : ∀ {L₁ L₂ L₃ : LanguageDef}
                   (f : Hom L₁ L₂) (g : Hom L₂ L₃) (ψ : Pattern → Prop),
                   ModeHom.mapPred (ModeHom.runtimeToBehavioral (comp f g)) ψ =
                     mapPred (comp f g) ψ

/-! ## The Witness -/

/-- MeTTa-IL, via OSLF, is a 2-mode adjoint doctrine fragment.

    All fields are direct applications of kernel-checked theorems proved
    in `Mode2Skeleton`, `MATTProvableNow`, and `ModeMapPredCommutingSquares`.
    No new proof obligations arise. -/
def mettaIL_2modeDocFrag : TwoModeAdjointDocFrag where
  modeId_left  := ModeHom.comp_id_left
  modeId_right := ModeHom.comp_id_right
  modeAssoc    := ModeHom.comp_assoc
  predId       := ModeHom.mapPred_id
  predComp     := ModeHom.mapPred_comp
  galoisAgrees := doctrine_galois_is_langGalois
  adjAgrees    := doctrine_adjunction_is_langModalAdjunction
  rtRtSquare   := runtime_runtime_square_coherence
  rtBehSquare  := runtime_behavioral_square_coherence

/-! ## The Capstone Theorem -/

/-- **MeTTa-IL is MaTT** (doctrinal/fibrational sense).

    MeTTa-IL equipped with its OSLF operational-semantic layer instantiates
    a 2-mode adjoint doctrine fragment:
    - Mode category `{pure, runtime(L), behavioral(L)}` with proved identity/associativity laws
    - Contravariant indexed predicate doctrine `ModeHom.mapPred` with proved functoriality
    - Modal adjunction ◇ ⊣ □ (`langDiamond ⊣ langBox`) at each behavioral mode
    - Beck-Chevalley commuting squares (mode-level = category-level pullback)

    See `TwoModeAdjointDocFrag` for the precise statement.
    See `MATTClaimMap` for the full conservative claim inventory. -/
theorem mettaIL_is_2mode_adjoint_doctrine : Nonempty TwoModeAdjointDocFrag :=
  ⟨mettaIL_2modeDocFrag⟩

/-! ## Anchor checks -/

#check @mettaIL_2modeDocFrag
#check @mettaIL_is_2mode_adjoint_doctrine
#check (mettaIL_2modeDocFrag.modeId_left)
#check (mettaIL_2modeDocFrag.predComp)
#check (mettaIL_2modeDocFrag.galoisAgrees)
#check (mettaIL_2modeDocFrag.rtRtSquare)
#check (mettaIL_2modeDocFrag.rtBehSquare)

end Mettapedia.OSLF.Framework.MATTFragment
