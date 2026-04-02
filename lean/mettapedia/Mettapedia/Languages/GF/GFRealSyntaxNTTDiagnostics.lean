import Algorithms.GF.Generated.PaperAmbiguitySig
import Mettapedia.Languages.GF.ConformanceCertificate
import Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses
import Mettapedia.Languages.GF.GeneratedBridgeConformance
import Mettapedia.Languages.GF.GFRealSyntaxBridge
import Mettapedia.Languages.GF.PGFWitnessIR
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Real GF Syntax → OSLF → NTT Diagnostics

Grounded diagnostics for the authoritative real-GF syntax lane:

- exported PGF witnesses are converted back to `RawTerm`,
- `GFCore.check` validates them against the real generated signature,
- `gfCheckedExprToPattern` lowers them into Lean patterns,
- `gfSyntaxLanguageDef` / `gfSyntaxLanguageDefFromList` supply the OSLF/NTT side.

This file intentionally avoids the authored semantic overlay. The resulting
modal story is correspondingly honest:

- constructor/native-type structure is rich and theorem-level;
- `□` is vacuously available because the syntax-only lane has no rewrites;
- `◇` has no positive witness until a grounded semantic reduction layer exists.
-/

namespace Mettapedia.Languages.GF.GFRealSyntaxNTTDiagnostics

open GFCore
open Mettapedia.Languages.GF.ConformanceCertificate
open Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses
open Mettapedia.Languages.GF.GeneratedBridgeConformance
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.Languages.GF.PGFWitnessIR
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- Kernel-reducible syntax-only PaperAmbiguity language from the literal function list. -/
def paperSyntaxLangKR : LanguageDef :=
  gfSyntaxLanguageDefFromList "PaperAmbiguity"
    Algorithms.GF.Generated.PaperAmbiguitySig.funsList

example : paperSyntaxLangKR.name = "PaperAmbiguity" := rfl
example : paperSyntaxLangKR.types.length = 16 := by decide
example : paperSyntaxLangKR.terms.length = 26 := by decide
example : paperSyntaxLangKR.equations = [] := rfl
example : paperSyntaxLangKR.rewrites = [] := rfl

def paperNSort : LangSort paperSyntaxLangKR :=
  LangSort.mk' paperSyntaxLangKR "N" (by decide)

def paperCNSort : LangSort paperSyntaxLangKR :=
  LangSort.mk' paperSyntaxLangKR "CN" (by decide)

def paperPNSort : LangSort paperSyntaxLangKR :=
  LangSort.mk' paperSyntaxLangKR "PN" (by decide)

def paperNPSort : LangSort paperSyntaxLangKR :=
  LangSort.mk' paperSyntaxLangKR "NP" (by decide)

def paperV2Sort : LangSort paperSyntaxLangKR :=
  LangSort.mk' paperSyntaxLangKR "V2" (by decide)

def paperVPSlashSort : LangSort paperSyntaxLangKR :=
  LangSort.mk' paperSyntaxLangKR "VPSlash" (by decide)

def paperSSort : LangSort paperSyntaxLangKR :=
  LangSort.mk' paperSyntaxLangKR "S" (by decide)

theorem useN_crossing :
    ("UseN", "N", "CN") ∈ unaryCrossings paperSyntaxLangKR := by
  decide

theorem usePN_crossing :
    ("UsePN", "PN", "NP") ∈ unaryCrossings paperSyntaxLangKR := by
  decide

theorem slashV2a_crossing :
    ("SlashV2a", "V2", "VPSlash") ∈ unaryCrossings paperSyntaxLangKR := by
  decide

def useNArrow : SortArrow paperSyntaxLangKR paperNSort paperCNSort :=
  ⟨"UseN", useN_crossing⟩

def usePNArrow : SortArrow paperSyntaxLangKR paperPNSort paperNPSort :=
  ⟨"UsePN", usePN_crossing⟩

def slashV2aArrow : SortArrow paperSyntaxLangKR paperV2Sort paperVPSlashSort :=
  ⟨"SlashV2a", slashV2a_crossing⟩

example : arrowSem paperSyntaxLangKR useNArrow manPattern = useNManPattern := rfl
example :
    arrowSem paperSyntaxLangKR usePNArrow (.apply "john_PN" []) = johnNPPattern := rfl
example :
    arrowSem paperSyntaxLangKR slashV2aArrow (.apply "see_V2" []) =
      .apply "SlashV2a" [.apply "see_V2" []] := rfl

abbrev PaperSyntaxNativeType := langNativeType paperSyntaxLangKR "S"

def paperPredicateType (sort : String) (φ : Pattern → Prop) : PaperSyntaxNativeType :=
  { sort := sort, pred := φ }

theorem paperSatisfiesType (p : Pattern) (nt : PaperSyntaxNativeType) :
    (langOSLF paperSyntaxLangKR "S").satisfies p nt.pred ↔ nt.pred p :=
  Iff.rfl

theorem paperSyntax_no_reduces {p q : Pattern} :
    ¬ langReduces paperSyntaxLangKR p q := by
  intro h
  cases h with
  | topRule r hr bs0 hbs0 bs hprem hq =>
      have hnil : r ∈ ([] : List RewriteRule) := by
        simp [paperSyntaxLangKR, gfSyntaxLanguageDefFromList, gfFunsListToLanguageDef] at hr
      cases hnil
  | congElem hct i hi r hr bs0 hbs0 bs hprem hq =>
      have hnil : r ∈ ([] : List RewriteRule) := by
        simp [paperSyntaxLangKR, gfSyntaxLanguageDefFromList, gfFunsListToLanguageDef] at hr
      cases hnil

theorem paperSyntax_no_diamond (φ : Pattern → Prop) (p : Pattern) :
    ¬ langDiamond paperSyntaxLangKR φ p := by
  intro h
  rcases (langDiamond_spec (lang := paperSyntaxLangKR) (φ := φ) (p := p)).1 h with
    ⟨q, hred, _⟩
  exact paperSyntax_no_reduces hred

theorem paperSyntax_vacuous_box (φ : Pattern → Prop) (p : Pattern) :
    langBox paperSyntaxLangKR φ p := by
  rw [langBox_spec]
  intro q hred
  exact False.elim (paperSyntax_no_reduces hred)

private def presTempPattern : Pattern :=
  .apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []]

private def theManNPPattern : Pattern :=
  .apply "DetCN" [.apply "the_Det" [], useNManPattern]

private def theTelescopeNPPattern : Pattern :=
  .apply "DetCN" [.apply "the_Det" [], .apply "UseN" [.apply "telescope_N" []]]

private def theBabyNPPattern : Pattern :=
  .apply "DetCN" [.apply "the_Det" [], .apply "UseN" [.apply "baby_N" []]]

private def theCribNPPattern : Pattern :=
  .apply "DetCN" [.apply "the_Det" [], .apply "UseN" [.apply "crib_N" []]]

private def withTelescopeAdvPattern : Pattern :=
  .apply "PrepNP" [.apply "with_Prep" [], theTelescopeNPPattern]

private def inCribAdvPattern : Pattern :=
  .apply "PrepNP" [.apply "in_Prep" [], theCribNPPattern]

/-- Real VP-attachment telescope pattern from the generated witness/check lane. -/
def telescopeVPPattern : Pattern :=
  .apply "UseCl"
    [ presTempPattern
    , .apply "PPos" []
    , .apply "PredVP"
        [ johnNPPattern
        , .apply "AdvVP"
            [ .apply "ComplSlash"
                [ .apply "SlashV2a" [.apply "see_V2" []]
                , theManNPPattern
                ]
            , withTelescopeAdvPattern
            ]
        ]
    ]

/-- Real NP-attachment telescope pattern from the generated witness/check lane. -/
def telescopeNPPattern : Pattern :=
  .apply "UseCl"
    [ presTempPattern
    , .apply "PPos" []
    , .apply "PredVP"
        [ johnNPPattern
        , .apply "ComplSlash"
            [ .apply "SlashV2a" [.apply "see_V2" []]
            , .apply "DetCN"
                [ .apply "the_Det" []
                , .apply "AdvCN" [useNManPattern, withTelescopeAdvPattern]
                ]
            ]
        ]
    ]

/-- Real VP-attachment Anna pattern from the generated witness/check lane. -/
def annaVPWitnessPattern : Pattern :=
  .apply "UseCl"
    [ presTempPattern
    , .apply "PPos" []
    , .apply "PredVP"
        [ annaNPPattern
        , .apply "AdvVP"
            [ .apply "ComplSlash"
                [ .apply "SlashV2a" [.apply "dress_V2" []]
                , theBabyNPPattern
                ]
            , inCribAdvPattern
            ]
        ]
    ]

/-- Real NP-attachment Anna pattern from the generated witness/check lane. -/
def annaNPWitnessPattern : Pattern :=
  .apply "UseCl"
    [ presTempPattern
    , .apply "PPos" []
    , .apply "PredVP"
        [ annaNPPattern
        , .apply "ComplSlash"
            [ .apply "SlashV2a" [.apply "dress_V2" []]
            , .apply "DetCN"
                [ .apply "the_Det" []
                , .apply "AdvCN"
                    [.apply "UseN" [.apply "baby_N" []], inCribAdvPattern]
                ]
            ]
        ]
    ]

def checkedWitnessPattern? (t : ExportedTree) : Option Pattern :=
  checkedPattern? t.toRawTerm

mutual
  def containsLabel (label : String) : Pattern → Bool
    | .bvar _ => false
    | .fvar _ => false
    | .apply f args => f == label || containsLabelList label args
    | .lambda _ body => containsLabel label body
    | .multiLambda _ _ body => containsLabel label body
    | .subst p q => containsLabel label p || containsLabel label q
    | .collection _ elems _ => containsLabelList label elems

  def containsLabelList (label : String) : List Pattern → Bool
    | [] => false
    | p :: ps => containsLabel label p || containsLabelList label ps
end

def vpAttachmentType : PaperSyntaxNativeType :=
  paperPredicateType "S" (fun p => containsLabel "AdvVP" p = true)

def npAttachmentType : PaperSyntaxNativeType :=
  paperPredicateType "S" (fun p => containsLabel "AdvCN" p = true)

example : containsLabel "AdvVP" telescopeVPPattern = true := by decide
example : containsLabel "AdvCN" telescopeVPPattern = false := by decide
example : containsLabel "AdvCN" telescopeNPPattern = true := by decide
example : containsLabel "AdvVP" telescopeNPPattern = false := by decide
example : containsLabel "AdvVP" annaVPWitnessPattern = true := by decide
example : containsLabel "AdvCN" annaNPWitnessPattern = true := by decide

theorem telescopeVP_satisfies_vpAttachmentType :
    (langOSLF paperSyntaxLangKR "S").satisfies telescopeVPPattern vpAttachmentType.pred := by
  show containsLabel "AdvVP" telescopeVPPattern = true
  decide

theorem telescopeVP_not_npAttachmentType :
    ¬ (langOSLF paperSyntaxLangKR "S").satisfies telescopeVPPattern npAttachmentType.pred := by
  show ¬ containsLabel "AdvCN" telescopeVPPattern = true
  decide

theorem telescopeNP_satisfies_npAttachmentType :
    (langOSLF paperSyntaxLangKR "S").satisfies telescopeNPPattern npAttachmentType.pred := by
  show containsLabel "AdvCN" telescopeNPPattern = true
  decide

theorem telescopeNP_not_vpAttachmentType :
    ¬ (langOSLF paperSyntaxLangKR "S").satisfies telescopeNPPattern vpAttachmentType.pred := by
  show ¬ containsLabel "AdvVP" telescopeNPPattern = true
  decide

theorem presentSentence_box_self :
    langBox paperSyntaxLangKR (fun q => q = presentSentencePattern) presentSentencePattern :=
  paperSyntax_vacuous_box _ _

theorem presentSentence_not_diamond_temporal :
    ¬ langDiamond paperSyntaxLangKR (fun q => q = temporalPresentPattern) presentSentencePattern :=
  paperSyntax_no_diamond _ _

private def ensureBool (label : String) (b : Bool) : IO Unit :=
  if b then
    IO.println s!"PASS: {label}"
  else
    throw <| IO.userError s!"FAIL: {label}"

#eval do
  ensureBool "english telescope witness 1 checks"
    (checkedWitnessPattern? englishTelescopeParse1 == some telescopeVPPattern)
  ensureBool "english telescope witness 2 checks"
    (checkedWitnessPattern? englishTelescopeParse2 == some telescopeNPPattern)
  ensureBool "czech telescope witness 1 checks"
    (checkedWitnessPattern? czechTelescopeParse1 == some telescopeVPPattern)
  ensureBool "czech telescope witness 2 checks"
    (checkedWitnessPattern? czechTelescopeParse2 == some telescopeNPPattern)
  ensureBool "english anna witness 1 checks"
    (checkedWitnessPattern? englishAnnaParse1 == some annaVPWitnessPattern)
  ensureBool "english anna witness 2 checks"
    (checkedWitnessPattern? englishAnnaParse2 == some annaNPWitnessPattern)
  ensureBool "czech anna witness 1 checks"
    (checkedWitnessPattern? czechAnnaParse1 == some annaVPWitnessPattern)
  ensureBool "czech anna witness 2 checks"
    (checkedWitnessPattern? czechAnnaParse2 == some annaNPWitnessPattern)

#eval do
  ensureBool "english/czech telescope reading 1 align after check"
    (checkedWitnessPattern? englishTelescopeParse1 == checkedWitnessPattern? czechTelescopeParse1)
  ensureBool "english/czech telescope reading 2 align after check"
    (checkedWitnessPattern? englishTelescopeParse2 == checkedWitnessPattern? czechTelescopeParse2)
  ensureBool "english/czech anna reading 1 align after check"
    (checkedWitnessPattern? englishAnnaParse1 == checkedWitnessPattern? czechAnnaParse1)
  ensureBool "english/czech anna reading 2 align after check"
    (checkedWitnessPattern? englishAnnaParse2 == checkedWitnessPattern? czechAnnaParse2)

#eval do
  ensureBool "syntax-only KR present sentence has no executable reductions"
    (rewriteWithContextWithPremises paperSyntaxLangKR presentSentencePattern == [])
  ensureBool "syntax-only KR telescope VP has no executable reductions"
    (rewriteWithContextWithPremises paperSyntaxLangKR telescopeVPPattern == [])

end Mettapedia.Languages.GF.GFRealSyntaxNTTDiagnostics
