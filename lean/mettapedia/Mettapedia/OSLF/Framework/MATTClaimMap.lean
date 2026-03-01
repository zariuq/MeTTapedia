import Mettapedia.OSLF.Framework.MATTProvableNow
import Mettapedia.OSLF.Framework.MATTFragment
import Mettapedia.OSLF.Framework.Mode2SkeletonLaws
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.LanguageMorphism

/-!
# MATTClaimMap

Conservative claim map for currently formalized MaTT-style structure in OSLF.
Scope is intentionally restricted to runtime/behavioral indexed doctrine,
morphism transport, and mode-skeleton coherence.
-/

namespace Mettapedia.OSLF.Framework.MATTClaimMap

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.LanguageEqCategory
open Mettapedia.OSLF.Framework.Mode2Skeleton
open Mettapedia.OSLF.Framework.ModeTheory
open Mettapedia.OSLF.Framework.MATTProvableNow
open Mettapedia.OSLF.Framework.Mode2SkeletonLaws
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism

/-- Conservative status marker for MaTT claims. -/
inductive MATTClaimStatus where
  | proven
  | intentionallyOutOfScope
  deriving DecidableEq, Repr

/-- One MaTT claim row with theorem anchor. -/
structure MATTClaim where
  claim : String
  leanRef : String
  status : MATTClaimStatus
  deriving DecidableEq, Repr

/-- Current theorem-indexed conservative MaTT claim map. -/
def mattClaimList : List MATTClaim :=
  [ ⟨"Per-language modal Galois connection in indexed doctrine",
      "doctrine_galois_is_langGalois", .proven⟩
  , ⟨"Per-language modal adjunction in indexed doctrine",
      "doctrine_adjunction_is_langModalAdjunction", .proven⟩
  , ⟨"Eq-category pullback functoriality",
      "eqCategory_mapPred_functorial", .proven⟩
  , ⟨"Mode-skeleton composition/predicate laws bundle",
      "Mode2SkeletonLaws.mode2SkeletonLaws", .proven⟩
  , ⟨"Runtime/runtime and runtime/behavioral commuting squares",
      "runtime_runtime_square_coherence + runtime_behavioral_square_coherence", .proven⟩
  , ⟨"Runtime morphism diamond witness transport",
      "runtime_mode_diamond_transport + runtime_mode_diamond_transport_comp", .proven⟩
  , ⟨"Pure mode isolation in current skeleton",
      "pure_mode_isolation", .proven⟩
  , ⟨"mettaPure runtime→behavioral diamond witness transport",
      "mettaPure_runtime_behavioral_transport", .proven⟩
  , ⟨"MeTTa-IL is a 2-mode adjoint doctrine fragment (TwoModeAdjointDocFrag)",
      "MATTFragment.mettaIL_2modeDocFrag", .proven⟩
  , ⟨"Full mode-2-category formalization",
      "intentionally omitted from current theorem scope", .intentionallyOutOfScope⟩
  , ⟨"Pure-mode morphism theory",
      "deferred until MeTTa-Pure bridge is completed", .intentionallyOutOfScope⟩
  ]

/-- Count claims by status. -/
def countByStatus (s : MATTClaimStatus) : Nat :=
  (mattClaimList.filter (fun c => c.status == s)).length

theorem provenCount_eq : countByStatus .proven = 9 := by
  decide

theorem outOfScopeCount_eq : countByStatus .intentionallyOutOfScope = 2 := by
  decide

/-- Pure-boundary theorem package in conservative MaTT scope. -/
theorem matt_pure_boundary_package
    {X Y : ModeObj} (f : ModeHom X Y) :
    X = .pure ∨ Y = .pure →
    X = .pure ∧ Y = .pure ∧ HEq f (ModeHom.id (X := .pure)) :=
  pure_mode_isolation f

/-- Canonical composed theorem linking doctrine, commuting squares,
and pullback functoriality with witness transport. -/
theorem matt_canonical_runtime_behavioral_package
    {L₁ L₂ L₃ : LanguageDef}
    (L : LanguageDef)
    (f : Hom L₁ L₂) (g : Hom L₂ L₃)
    (ψ : Pattern → Prop)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    mettaILRuntimeBehavioralDoctrine.galois L = langGalois L ∧
    mettaILRuntimeBehavioralDoctrine.modalAdjunction L =
      Mettapedia.OSLF.Framework.CategoryBridge.langModalAdjunction L ∧
    mapPred (comp f g) ψ = mapPred f (mapPred g ψ) ∧
    ModeHom.mapPred (ModeHom.runtimeMap (comp f g)) ψ =
      mapPred (comp f g) ψ ∧
    ModeHom.mapPred (ModeHom.runtimeToBehavioral (comp f g)) ψ =
      mapPred (comp f g) ψ ∧
    (∃ q, langReduces L₁ p q ∧ φ q ∧
      ∃ T, LangReducesStar L₃ ((comp f g).mapTerm p) T ∧
        T = (comp f g).mapTerm q) := by
  refine ⟨doctrine_galois_eq L, doctrine_modalAdjunction_eq L, ?_, ?_, ?_, ?_⟩
  · exact Mettapedia.OSLF.Framework.LanguageEqCategoryLaws.mapPred_comp_holds f g ψ
  · exact runtime_runtime_square_coherence f g ψ
  · exact runtime_behavioral_square_coherence f g ψ
  · exact runtime_mode_diamond_transport_comp f g h

/-! ## Anchor checks -/

#check @doctrine_galois_is_langGalois
#check @doctrine_adjunction_is_langModalAdjunction
#check @eqCategory_mapPred_functorial
#check @Mode2SkeletonLaws.mode2SkeletonLaws
#check @runtime_runtime_square_coherence
#check @runtime_behavioral_square_coherence
#check @runtime_mode_diamond_transport
#check @runtime_mode_diamond_transport_comp
#check @pure_mode_isolation
#check @mettaPure_runtime_behavioral_transport
#check @matt_pure_boundary_package
#check @matt_canonical_runtime_behavioral_package

end Mettapedia.OSLF.Framework.MATTClaimMap
