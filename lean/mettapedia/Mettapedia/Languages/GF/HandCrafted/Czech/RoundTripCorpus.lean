import Mettapedia.Languages.GF.HandCrafted.Czech.Tests

/-!
# Czech Linearization Roundtrip Corpus

Restricted roundtrip over a theorem-backed Czech form corpus (drawn from the
proved declension examples in `Czech/Tests.lean`).

This remains corpus-restricted by design: parsing succeeds exactly on the
validated linearizations and is proved complete/sound for this corpus.
-/

namespace Mettapedia.Languages.GF.HandCrafted.Czech.RoundTripCorpus

open Mettapedia.Languages.GF.HandCrafted.Czech
open Mettapedia.Languages.GF.HandCrafted.Czech.Declensions

inductive ExampleTree where
  | panNomSg
  | panGenSg
  | panVocSg
  | panNomPl
  | zenaGenPl
  | mestoNomSg
  | mestoGenSg
  | muzGenSg
  | klukNomPl
  | predsedaVocSg
  | soudceNomSg
  | strojGenSg
  | ruzeInsPl
  | pisenGenSg
  | kostNomPl
  | kureNomPl
  | moreInsSg
  | staveniLocPl
  deriving DecidableEq, Repr

private def pán : CzechNoun := declPAN "pán"
private def žena : CzechNoun := declZENA "žena"
private def město : CzechNoun := declMESTO "město"
private def muž : CzechNoun := declMUZ "muž"
private def kluk : CzechNoun := declPAN "kluk"
private def předseda : CzechNoun := declPREDSEDA "předseda"
private def soudce : CzechNoun := declSOUDCE "soudce"
private def stroj : CzechNoun := declSTROJ "stroj"
private def růže : CzechNoun := declRUZE "růže"
private def píseň : CzechNoun := declPISEN "píseň"
private def kost : CzechNoun := declKOST "kost"
private def kuře : CzechNoun := declKURE "kuře"
private def moře : CzechNoun := declMORE "moře"
private def stavení : CzechNoun := declSTAVENI "stavení"

/-- Grammar-level linearization (declension form selection) per curated example. -/
def linearizeExample : ExampleTree → String
  | .panNomSg => declineFull pán ⟨Case.Nom, Number.Sg⟩
  | .panGenSg => declineFull pán ⟨Case.Gen, Number.Sg⟩
  | .panVocSg => declineFull pán ⟨Case.Voc, Number.Sg⟩
  | .panNomPl => declineFull pán ⟨Case.Nom, Number.Pl⟩
  | .zenaGenPl => declineFull žena ⟨Case.Gen, Number.Pl⟩
  | .mestoNomSg => declineFull město ⟨Case.Nom, Number.Sg⟩
  | .mestoGenSg => declineFull město ⟨Case.Gen, Number.Sg⟩
  | .muzGenSg => declineFull muž ⟨Case.Gen, Number.Sg⟩
  | .klukNomPl => declineFull kluk ⟨Case.Nom, Number.Pl⟩
  | .predsedaVocSg => declineFull předseda ⟨Case.Voc, Number.Sg⟩
  | .soudceNomSg => declineFull soudce ⟨Case.Nom, Number.Sg⟩
  | .strojGenSg => declineFull stroj ⟨Case.Gen, Number.Sg⟩
  | .ruzeInsPl => declineFull růže ⟨Case.Ins, Number.Pl⟩
  | .pisenGenSg => declineFull píseň ⟨Case.Gen, Number.Sg⟩
  | .kostNomPl => declineFull kost ⟨Case.Nom, Number.Pl⟩
  | .kureNomPl => declineFull kuře ⟨Case.Nom, Number.Pl⟩
  | .moreInsSg => declineFull moře ⟨Case.Ins, Number.Sg⟩
  | .staveniLocPl => declineFull stavení ⟨Case.Loc, Number.Pl⟩

/-- Full curated Czech corpus used by the roundtrip parser. -/
def allExamples : List ExampleTree :=
  [ .panNomSg
  , .panGenSg
  , .panVocSg
  , .panNomPl
  , .zenaGenPl
  , .mestoNomSg
  , .mestoGenSg
  , .muzGenSg
  , .klukNomPl
  , .predsedaVocSg
  , .soudceNomSg
  , .strojGenSg
  , .ruzeInsPl
  , .pisenGenSg
  , .kostNomPl
  , .kureNomPl
  , .moreInsSg
  , .staveniLocPl
  ]

/-- Every example constructor appears in the curated corpus list. -/
theorem mem_allExamples (e : ExampleTree) : e ∈ allExamples := by
  cases e <;> simp [allExamples]

/-- Canonical parser for the validated corpus (returns all matching analyses). -/
def parseLinearization : String → List ExampleTree
  | s => allExamples.filter (fun e => linearizeExample e = s)

/-- Corpus completeness: parsing linearization recovers the source analysis. -/
theorem parse_linearize_complete (e : ExampleTree) :
    e ∈ parseLinearization (linearizeExample e) := by
  refine List.mem_filter.mpr ?_
  exact ⟨mem_allExamples e, by simp⟩

/-- Corpus soundness: any parsed analysis linearizes back to the input text. -/
theorem parse_sound (s : String) (e : ExampleTree) :
    e ∈ parseLinearization s → linearizeExample e = s := by
  intro h
  simpa using (List.mem_filter.mp h).2

/-- Negative example: unknown text has no analysis in this corpus parser. -/
theorem parse_unknown_empty : parseLinearization "nesmyslny-vstup" = [] := by
  decide

/-- Representative corpus entries are uniquely parsed in this restricted parser. -/
theorem distinct_linearization_examples :
    (parseLinearization "pán").length = 1 ∧
    (parseLinearization "pane").length = 1 ∧
    (parseLinearization "staveních").length = 1 := by
  decide

end Mettapedia.Languages.GF.HandCrafted.Czech.RoundTripCorpus

