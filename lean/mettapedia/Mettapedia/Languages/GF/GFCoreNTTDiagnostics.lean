import Mettapedia.Languages.GF.GFRealSyntaxNTTDiagnostics
import Mettapedia.Languages.GF.GeneratedBridgeConformance
import Mettapedia.OSLF.Framework.CategoryBridge

/-!
# Real GFCore OSLF → NTT Diagnostics

Compatibility-facing diagnostics for the authoritative real GF syntax lane.

This module now re-exports the grounded `PaperAmbiguity` witness/check facts from
`GFRealSyntaxNTTDiagnostics` and adds one representable-fiber readout theorem that
is still useful for downstream summaries.

What this module no longer does:
- it no longer claims a positive semantic reduction witness for GF;
- it no longer depends on the authored semantic overlay.

Positive examples:
- the real `PaperAmbiguity` syntax object has theorem-level constructor/category
  structure;
- checked GF witnesses from English and Czech align to the same Lean patterns;
- the representable presheaf fiber contains the checked present-sentence seed.

Negative example:
- the syntax-only GF lane has no executable reductions, so there is no honest
  positive `◇` witness here.
-/

namespace Mettapedia.Languages.GF.GFCoreNTTDiagnostics

open Mettapedia.Languages.GF.GFRealSyntaxNTTDiagnostics
open Mettapedia.Languages.GF.GeneratedBridgeConformance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory

abbrev paperLangKR : LanguageDef := paperSyntaxLangKR

abbrev paperNSort : LangSort paperLangKR := GFRealSyntaxNTTDiagnostics.paperNSort
abbrev paperCNSort : LangSort paperLangKR := GFRealSyntaxNTTDiagnostics.paperCNSort
abbrev paperPNSort : LangSort paperLangKR := GFRealSyntaxNTTDiagnostics.paperPNSort
abbrev paperNPSort : LangSort paperLangKR := GFRealSyntaxNTTDiagnostics.paperNPSort
abbrev paperV2Sort : LangSort paperLangKR := GFRealSyntaxNTTDiagnostics.paperV2Sort
abbrev paperVPSlashSort : LangSort paperLangKR := GFRealSyntaxNTTDiagnostics.paperVPSlashSort
abbrev paperSSort : LangSort paperLangKR := GFRealSyntaxNTTDiagnostics.paperSSort

abbrev useN_crossing : ("UseN", "N", "CN") ∈ unaryCrossings paperLangKR :=
  GFRealSyntaxNTTDiagnostics.useN_crossing

abbrev usePN_crossing : ("UsePN", "PN", "NP") ∈ unaryCrossings paperLangKR :=
  GFRealSyntaxNTTDiagnostics.usePN_crossing

abbrev slashV2a_crossing : ("SlashV2a", "V2", "VPSlash") ∈ unaryCrossings paperLangKR :=
  GFRealSyntaxNTTDiagnostics.slashV2a_crossing

abbrev useNArrow : SortArrow paperLangKR paperNSort paperCNSort :=
  GFRealSyntaxNTTDiagnostics.useNArrow

abbrev usePNArrow : SortArrow paperLangKR paperPNSort paperNPSort :=
  GFRealSyntaxNTTDiagnostics.usePNArrow

abbrev slashV2aArrow : SortArrow paperLangKR paperV2Sort paperVPSlashSort :=
  GFRealSyntaxNTTDiagnostics.slashV2aArrow

def useNMor : ConstructorObj.mk paperNSort ⟶ ConstructorObj.mk paperCNSort :=
  useNArrow.toPath

def usePNMor : ConstructorObj.mk paperPNSort ⟶ ConstructorObj.mk paperNPSort :=
  usePNArrow.toPath

def slashV2aMor : ConstructorObj.mk paperV2Sort ⟶ ConstructorObj.mk paperVPSlashSort :=
  slashV2aArrow.toPath

abbrev PaperSyntaxNativeType := GFRealSyntaxNTTDiagnostics.PaperSyntaxNativeType
abbrev paperPredicateType := GFRealSyntaxNTTDiagnostics.paperPredicateType
abbrev paperSatisfiesType := GFRealSyntaxNTTDiagnostics.paperSatisfiesType

abbrev telescopeVPPattern := GFRealSyntaxNTTDiagnostics.telescopeVPPattern
abbrev telescopeNPPattern := GFRealSyntaxNTTDiagnostics.telescopeNPPattern
abbrev annaVPWitnessPattern := GFRealSyntaxNTTDiagnostics.annaVPWitnessPattern
abbrev annaNPWitnessPattern := GFRealSyntaxNTTDiagnostics.annaNPWitnessPattern
abbrev presentSentencePattern := GeneratedBridgeConformance.presentSentencePattern
abbrev temporalPresentPattern := GeneratedBridgeConformance.temporalPresentPattern

abbrev vpAttachmentType := GFRealSyntaxNTTDiagnostics.vpAttachmentType
abbrev npAttachmentType := GFRealSyntaxNTTDiagnostics.npAttachmentType

abbrev telescopeVP_satisfies_vpAttachmentType :=
  GFRealSyntaxNTTDiagnostics.telescopeVP_satisfies_vpAttachmentType

abbrev telescopeVP_not_npAttachmentType :=
  GFRealSyntaxNTTDiagnostics.telescopeVP_not_npAttachmentType

abbrev telescopeNP_satisfies_npAttachmentType :=
  GFRealSyntaxNTTDiagnostics.telescopeNP_satisfies_npAttachmentType

abbrev telescopeNP_not_vpAttachmentType :=
  GFRealSyntaxNTTDiagnostics.telescopeNP_not_vpAttachmentType

abbrev presentSentence_box_self := GFRealSyntaxNTTDiagnostics.presentSentence_box_self
abbrev presentSentence_not_diamond_temporal :=
  GFRealSyntaxNTTDiagnostics.presentSentence_not_diamond_temporal

def presentSentenceOrbitPred (p : Pattern) : Prop :=
  ∃ a : LangSort paperLangKR, ∃ h : SortPath paperLangKR a paperSSort,
    p = pathSem paperLangKR h presentSentencePattern

theorem presentSentenceOrbit_natural :
    languageSortPredNaturality paperLangKR paperSSort presentSentencePattern
      presentSentenceOrbitPred := by
  intro a b g h _
  exact ⟨a, g.comp h, rfl⟩

noncomputable def paperPresentSentenceOrbitFiber : languageSortFiber paperLangKR paperSSort :=
  languageSortFiber_ofPatternPred paperLangKR paperSSort presentSentencePattern
    presentSentenceOrbitPred
    presentSentenceOrbit_natural

def paperSId :
    (languageSortRepresentableObj paperLangKR paperSSort).obj
      (Opposite.op (ConstructorObj.mk paperSSort)) :=
  SortPath.nil

theorem paperPresentSentenceOrbitFiber_characteristic_roundtrip :
    (languageSortFiber_characteristicEquiv (lang := paperLangKR) (s := paperSSort))
      (languageSortFiber_ofPatternPred_characteristicMap
        paperLangKR paperSSort presentSentencePattern
        presentSentenceOrbitPred
        presentSentenceOrbit_natural) =
    paperPresentSentenceOrbitFiber := by
  simpa [paperPresentSentenceOrbitFiber] using
    (languageSortFiber_ofPatternPred_characteristicMap_spec
      paperLangKR paperSSort presentSentencePattern
      presentSentenceOrbitPred
      presentSentenceOrbit_natural)

theorem paperPresentSentenceOrbitFiber_contains_seed :
    paperSId ∈
      paperPresentSentenceOrbitFiber.obj (Opposite.op (ConstructorObj.mk paperSSort)) := by
  change paperSId ∈
      (languageSortFiber_ofPatternPred paperLangKR paperSSort presentSentencePattern
        presentSentenceOrbitPred presentSentenceOrbit_natural).obj
        (Opposite.op (ConstructorObj.mk paperSSort))
  rw [languageSortFiber_ofPatternPred_mem_iff]
  exact ⟨paperSSort, SortPath.nil, by simp [paperSId, pathSem]⟩

end Mettapedia.Languages.GF.GFCoreNTTDiagnostics
