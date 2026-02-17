import Mettapedia.Languages.GF.Czech.Tests

/-!
# Czech Surface Roundtrip Corpus

Restricted roundtrip over a theorem-backed Czech form corpus (drawn from the
proved declension examples in `Czech/Tests.lean`).

This remains corpus-restricted by design: parsing succeeds exactly on the
validated surfaces and is proved complete/sound for this corpus.
-/

namespace Mettapedia.Languages.GF.Czech.RoundTripCorpus

open Mettapedia.Languages.GF.Czech
open Mettapedia.Languages.GF.Czech.Declensions

inductive ExampleSurface where
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
def linearizeSurface : ExampleSurface → String
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
def allExamples : List ExampleSurface :=
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

/-- Every surface constructor appears in the curated corpus list. -/
theorem mem_allExamples (e : ExampleSurface) : e ∈ allExamples := by
  cases e <;> simp [allExamples]

/-- Canonical parser for the validated corpus (returns all matching analyses). -/
def parseSurface : String → List ExampleSurface
  | s => allExamples.filter (fun e => linearizeSurface e = s)

/-- Corpus completeness: parsing linearization recovers the source analysis. -/
theorem parse_linearize_complete (e : ExampleSurface) :
    e ∈ parseSurface (linearizeSurface e) := by
  refine List.mem_filter.mpr ?_
  exact ⟨mem_allExamples e, by simp⟩

/-- Corpus soundness: any parsed analysis linearizes back to the input surface. -/
theorem parse_sound (s : String) (e : ExampleSurface) :
    e ∈ parseSurface s → linearizeSurface e = s := by
  intro h
  simpa using (List.mem_filter.mp h).2

/-- Negative example: unknown surface has no analysis in this corpus parser. -/
theorem parse_unknown_empty : parseSurface "nesmyslny-vstup" = [] := by
  decide

/-- Representative corpus entries are uniquely parsed in this restricted parser. -/
theorem distinct_surface_examples :
    (parseSurface "pán").length = 1 ∧
    (parseSurface "pane").length = 1 ∧
    (parseSurface "staveních").length = 1 := by
  decide

end Mettapedia.Languages.GF.Czech.RoundTripCorpus

