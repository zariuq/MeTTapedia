import Mettapedia.Languages.GF.GeneratedBridgeConformance
import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Real GFCore OSLF → NTT Diagnostics

This module extracts small but concrete NTT-facing facts from the real
GFCore-backed GF bridge.

Positive examples:
- `UseN : N → CN` and `PassV2 : V2 → VP` show up as genuine constructor-category
  morphisms induced by the real generated signature.
- The checked present-tense sentence sits in the canonical presheaf fiber of the
  modal predicate “can reduce to the temporalized sentence”.

Negative example:
- we do not invent a shadow grammar or a hand-authored toy fragment here; every
  witness is built from `PaperAmbiguitySig` through the real bridge.
-/

namespace Mettapedia.Languages.GF.GFCoreNTTDiagnostics

open Mettapedia.Languages.GF.GeneratedBridgeConformance
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory

def paperNSort : LangSort paperLang :=
  LangSort.mk' paperLang "N" (by native_decide)

def paperCNSort : LangSort paperLang :=
  LangSort.mk' paperLang "CN" (by native_decide)

def paperV2Sort : LangSort paperLang :=
  LangSort.mk' paperLang "V2" (by native_decide)

def paperVPSort : LangSort paperLang :=
  LangSort.mk' paperLang "VP" (by native_decide)

def paperSSort : LangSort paperLang :=
  LangSort.mk' paperLang "S" (by native_decide)

theorem useN_crossing :
    ("UseN", "N", "CN") ∈ unaryCrossings paperLang := by
  native_decide

theorem passV2_crossing :
    ("PassV2", "V2", "VP") ∈ unaryCrossings paperLang := by
  native_decide

def useNArrow : SortArrow paperLang paperNSort paperCNSort :=
  ⟨"UseN", useN_crossing⟩

def passV2Arrow : SortArrow paperLang paperV2Sort paperVPSort :=
  ⟨"PassV2", passV2_crossing⟩

def useNMor : ConstructorObj.mk paperNSort ⟶ ConstructorObj.mk paperCNSort :=
  useNArrow.toPath

def passV2Mor : ConstructorObj.mk paperV2Sort ⟶ ConstructorObj.mk paperVPSort :=
  passV2Arrow.toPath

example : arrowSem paperLang useNArrow manPattern = useNManPattern := rfl

example :
    arrowSem paperLang passV2Arrow (.apply "see_V2" []) =
      .apply "PassV2" [.apply "see_V2" []] := rfl

def temporalReachabilityPred : Pattern → Prop :=
  langDiamond paperLang (fun q => q = temporalPresentPattern)

theorem presentSentence_diamond_temporal :
    temporalReachabilityPred presentSentencePattern := by
  rw [temporalReachabilityPred, langDiamond_spec]
  refine ⟨temporalPresentPattern, ?_, rfl⟩
  apply exec_to_langReducesUsing (relEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
    (lang := paperLang)
  simpa [langReducesExecUsing] using
    (show temporalPresentPattern ∈ rewriteWithContextWithPremises paperLang presentSentencePattern from by
      native_decide)

def presentSentenceOrbitPred (p : Pattern) : Prop :=
  ∃ a : LangSort paperLang, ∃ h : SortPath paperLang a paperSSort,
    p = pathSem paperLang h presentSentencePattern

theorem presentSentenceOrbit_natural :
    languageSortPredNaturality paperLang paperSSort presentSentencePattern
      presentSentenceOrbitPred := by
  intro a _ g h _
  exact ⟨a, g.comp h, rfl⟩

noncomputable def paperPresentSentenceOrbitFiber : languageSortFiber paperLang paperSSort :=
  languageSortFiber_ofPatternPred paperLang paperSSort presentSentencePattern
    presentSentenceOrbitPred
    presentSentenceOrbit_natural

def paperSId :
    (languageSortRepresentableObj paperLang paperSSort).obj
      (Opposite.op (ConstructorObj.mk paperSSort)) :=
  SortPath.nil

theorem paperPresentSentenceOrbitFiber_characteristic_roundtrip :
    (languageSortFiber_characteristicEquiv (lang := paperLang) (s := paperSSort))
      (languageSortFiber_ofPatternPred_characteristicMap
        paperLang paperSSort presentSentencePattern
        presentSentenceOrbitPred
        presentSentenceOrbit_natural) =
    paperPresentSentenceOrbitFiber := by
  simpa [paperPresentSentenceOrbitFiber] using
    (languageSortFiber_ofPatternPred_characteristicMap_spec
      paperLang paperSSort presentSentencePattern
      presentSentenceOrbitPred
      presentSentenceOrbit_natural)

theorem paperPresentSentenceOrbitFiber_contains_seed :
    paperSId ∈
      paperPresentSentenceOrbitFiber.obj (Opposite.op (ConstructorObj.mk paperSSort)) := by
  change paperSId ∈
      (languageSortFiber_ofPatternPred paperLang paperSSort presentSentencePattern
        presentSentenceOrbitPred presentSentenceOrbit_natural).obj
        (Opposite.op (ConstructorObj.mk paperSSort))
  rw [languageSortFiber_ofPatternPred_mem_iff]
  exact ⟨paperSSort, SortPath.nil, by simp [paperSId, pathSem]⟩

end Mettapedia.Languages.GF.GFCoreNTTDiagnostics
