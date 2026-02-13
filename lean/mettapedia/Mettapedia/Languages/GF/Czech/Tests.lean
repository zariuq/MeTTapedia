/-
# Czech Declension: Regression Tests

Proper assertions that FAIL when declensions are wrong.

## Test Strategy
- Use `decide` for exact string equality (kernel-reducible string ops)
- Document expected forms from GF-RGL and Czech grammar references

## Known Issues (as of 2026-02-13)
1. "pes" genitive: produces "pese", should be "psa" (irregular stem alternation)
2. "okno" gen pl: produces "okn", should be "oken" (epenthetic e for consonant clusters)
-/

import Mettapedia.Languages.GF.Czech.Declensions

namespace Mettapedia.Languages.GF.Czech.Tests

open Mettapedia.Languages.GF.Czech
open Declensions

/-! ## Test: PAN Paradigm (Masculine Animate Hard)
    Source: GF ResCze.gf lines 181-195, CEG §3.5.1
-/

def pán := declPAN "pán"

-- Singular
example : declineFull pán ⟨Case.Nom, Number.Sg⟩ = "pán" := by decide
example : declineFull pán ⟨Case.Gen, Number.Sg⟩ = "pána" := by decide
example : declineFull pán ⟨Case.Dat, Number.Sg⟩ = "pánovi" := by decide
example : declineFull pán ⟨Case.Acc, Number.Sg⟩ = "pána" := by decide
example : declineFull pán ⟨Case.Voc, Number.Sg⟩ = "pane" := by decide
example : declineFull pán ⟨Case.Loc, Number.Sg⟩ = "pánovi" := by decide
example : declineFull pán ⟨Case.Ins, Number.Sg⟩ = "pánem" := by decide

-- Plural
example : declineFull pán ⟨Case.Nom, Number.Pl⟩ = "páni" := by decide
example : declineFull pán ⟨Case.Gen, Number.Pl⟩ = "pánů" := by decide
example : declineFull pán ⟨Case.Dat, Number.Pl⟩ = "pánům" := by decide
example : declineFull pán ⟨Case.Acc, Number.Pl⟩ = "pány" := by decide
example : declineFull pán ⟨Case.Loc, Number.Pl⟩ = "pánech" := by decide
example : declineFull pán ⟨Case.Ins, Number.Pl⟩ = "pány" := by decide

/-! ## Test: HRAD Paradigm (Masculine Inanimate Hard)
    Source: GF ResCze.gf lines 219-234, CEG §3.5.2
-/

def hrad := declHRAD "hrad"

example : declineFull hrad ⟨Case.Nom, Number.Sg⟩ = "hrad" := by decide
example : declineFull hrad ⟨Case.Gen, Number.Sg⟩ = "hradu" := by decide
-- Inanimate: Acc = Nom
example : declineFull hrad ⟨Case.Acc, Number.Sg⟩ = "hrad" := by decide

/-! ## Test: ZENA Paradigm (Feminine)
    Source: GF ResCze.gf lines 236-253, CEG §3.6.1
-/

def žena := declZENA "žena"

example : declineFull žena ⟨Case.Nom, Number.Sg⟩ = "žena" := by decide
example : declineFull žena ⟨Case.Gen, Number.Sg⟩ = "ženy" := by decide
example : declineFull žena ⟨Case.Acc, Number.Sg⟩ = "ženu" := by decide
example : declineFull žena ⟨Case.Ins, Number.Sg⟩ = "ženou" := by decide

-- Plural genitive = bare stem (key compression feature)
example : declineFull žena ⟨Case.Gen, Number.Pl⟩ = "žen" := by decide

/-! ## Test: MESTO Paradigm (Neuter)
    Source: GF ResCze.gf lines 255-271, CEG §3.7.1
-/

def město := declMESTO "město"

example : declineFull město ⟨Case.Nom, Number.Sg⟩ = "město" := by decide
example : declineFull město ⟨Case.Gen, Number.Sg⟩ = "města" := by decide
-- Neuter syncretism: Nom = Acc = Voc
example : declineFull město ⟨Case.Acc, Number.Sg⟩ = "město" := by decide
example : declineFull město ⟨Case.Voc, Number.Sg⟩ = "město" := by decide

/-! ## Test: MUZ Paradigm (Masculine Animate Soft)
    Source: GF ResCze.gf lines 273-296, CEG §3.5.3
-/

def muž := declMUZ "muž"

example : declineFull muž ⟨Case.Nom, Number.Sg⟩ = "muž" := by decide
example : declineFull muž ⟨Case.Gen, Number.Sg⟩ = "muže" := by decide
example : declineFull muž ⟨Case.Dat, Number.Sg⟩ = "muži" := by decide

/-! ## Test: Palatalization Rules -/

def kluk := declPAN "kluk"

-- k → c before -i (palatalization)
example : declineFull kluk ⟨Case.Nom, Number.Pl⟩ = "kluci" := by decide

-- h → z before -i
def vrh := declPAN "vrh"
example : declineFull vrh ⟨Case.Nom, Number.Pl⟩ = "vrzi" := by decide

/-! ## Test: Vocative Shortening -/

-- á → a in vocative (vowel shortening)
example : declineFull pán ⟨Case.Voc, Number.Sg⟩ = "pane" := by decide

/-! ## Test: Syncretism Detection -/

-- Now kernel-reducible (no more partial functions blocking)
example : hasSyncretism pán = true := by decide
example : hasSyncretism žena = true := by decide
example : hasSyncretism město = true := by decide

/-! ## Test: PREDSEDA Paradigm (Masculine Animate -a)
    Source: GF ResCze.gf lines 197-217
-/

def předseda := declPREDSEDA "předseda"

example : declineFull předseda ⟨Case.Nom, Number.Sg⟩ = "předseda" := by decide
example : declineFull předseda ⟨Case.Gen, Number.Sg⟩ = "předsedy" := by decide
example : declineFull předseda ⟨Case.Acc, Number.Sg⟩ = "předsedu" := by decide
example : declineFull předseda ⟨Case.Voc, Number.Sg⟩ = "předsedo" := by decide
example : declineFull předseda ⟨Case.Ins, Number.Sg⟩ = "předsedou" := by decide
example : declineFull předseda ⟨Case.Nom, Number.Pl⟩ = "předsedové" := by decide

/-! ## Test: SOUDCE Paradigm (Masculine Animate -ce)
    Source: GF ResCze.gf lines 298-313
-/

def soudce := declSOUDCE "soudce"

-- High syncretism: Nom/Gen/Acc/Voc all = "soudce"
example : declineFull soudce ⟨Case.Nom, Number.Sg⟩ = "soudce" := by decide
example : declineFull soudce ⟨Case.Gen, Number.Sg⟩ = "soudce" := by decide
example : declineFull soudce ⟨Case.Acc, Number.Sg⟩ = "soudce" := by decide
example : declineFull soudce ⟨Case.Dat, Number.Sg⟩ = "soudci" := by decide
example : declineFull soudce ⟨Case.Ins, Number.Sg⟩ = "soudcem" := by decide
example : declineFull soudce ⟨Case.Nom, Number.Pl⟩ = "soudci" := by decide
example : declineFull soudce ⟨Case.Acc, Number.Pl⟩ = "soudce" := by decide

/-! ## Test: STROJ Paradigm (Masculine Inanimate Soft)
    Source: GF ResCze.gf lines 315-328
-/

def stroj := declSTROJ "stroj"

example : declineFull stroj ⟨Case.Nom, Number.Sg⟩ = "stroj" := by decide
example : declineFull stroj ⟨Case.Gen, Number.Sg⟩ = "stroje" := by decide
-- Inanimate: Acc = Nom
example : declineFull stroj ⟨Case.Acc, Number.Sg⟩ = "stroj" := by decide
example : declineFull stroj ⟨Case.Dat, Number.Sg⟩ = "stroji" := by decide
example : declineFull stroj ⟨Case.Ins, Number.Sg⟩ = "strojem" := by decide
example : declineFull stroj ⟨Case.Nom, Number.Pl⟩ = "stroje" := by decide

/-! ## Test: RUZE Paradigm (Feminine Soft -e)
    Source: GF ResCze.gf lines 330-344
-/

def růže := declRUZE "růže"

example : declineFull růže ⟨Case.Nom, Number.Sg⟩ = "růže" := by decide
example : declineFull růže ⟨Case.Gen, Number.Sg⟩ = "růže" := by decide
example : declineFull růže ⟨Case.Acc, Number.Sg⟩ = "růži" := by decide
example : declineFull růže ⟨Case.Ins, Number.Sg⟩ = "růží" := by decide
-- Plural genitive uses shortFemPlGen
example : declineFull růže ⟨Case.Gen, Number.Pl⟩ = "růží" := by decide
example : declineFull růže ⟨Case.Ins, Number.Pl⟩ = "růžemi" := by decide

/-! ## Test: PISEN Paradigm (Feminine Soft Consonant)
    Source: GF ResCze.gf lines 346-361
-/

def píseň := declPISEN "píseň"

example : declineFull píseň ⟨Case.Nom, Number.Sg⟩ = "píseň" := by decide
example : declineFull píseň ⟨Case.Gen, Number.Sg⟩ = "písně" := by decide
example : declineFull píseň ⟨Case.Dat, Number.Sg⟩ = "písni" := by decide
example : declineFull píseň ⟨Case.Ins, Number.Sg⟩ = "písní" := by decide
example : declineFull píseň ⟨Case.Nom, Number.Pl⟩ = "písně" := by decide
example : declineFull píseň ⟨Case.Gen, Number.Pl⟩ = "písní" := by decide

/-! ## Test: KOST Paradigm (Feminine -ost)
    Source: GF ResCze.gf lines 363-375
-/

def kost := declKOST "kost"

example : declineFull kost ⟨Case.Nom, Number.Sg⟩ = "kost" := by decide
example : declineFull kost ⟨Case.Gen, Number.Sg⟩ = "kosti" := by decide
-- Nom = Acc (like inanimate pattern)
example : declineFull kost ⟨Case.Acc, Number.Sg⟩ = "kost" := by decide
example : declineFull kost ⟨Case.Ins, Number.Sg⟩ = "kostí" := by decide
example : declineFull kost ⟨Case.Nom, Number.Pl⟩ = "kosti" := by decide
example : declineFull kost ⟨Case.Ins, Number.Pl⟩ = "kostmi" := by decide

/-! ## Test: KURE Paradigm (Neuter, -e stem with -ete genitive)
    Source: GF ResCze.gf lines 377-392
-/

def kuře := declKURE "kuře"

example : declineFull kuře ⟨Case.Nom, Number.Sg⟩ = "kuře" := by decide
example : declineFull kuře ⟨Case.Gen, Number.Sg⟩ = "kuřete" := by decide
example : declineFull kuře ⟨Case.Dat, Number.Sg⟩ = "kuřeti" := by decide
example : declineFull kuře ⟨Case.Ins, Number.Sg⟩ = "kuřetem" := by decide
-- Plural: -ata paradigm
example : declineFull kuře ⟨Case.Nom, Number.Pl⟩ = "kuřata" := by decide
example : declineFull kuře ⟨Case.Gen, Number.Pl⟩ = "kuřat" := by decide
example : declineFull kuře ⟨Case.Ins, Number.Pl⟩ = "kuřaty" := by decide

/-! ## Test: MORE Paradigm (Neuter Soft, ending in e)
    Source: GF ResCze.gf lines 394-408
-/

def moře := declMORE "moře"

-- Very high syncretism: Nom/Gen/Acc/Voc all = "moře"
example : declineFull moře ⟨Case.Nom, Number.Sg⟩ = "moře" := by decide
example : declineFull moře ⟨Case.Gen, Number.Sg⟩ = "moře" := by decide
example : declineFull moře ⟨Case.Dat, Number.Sg⟩ = "moři" := by decide
example : declineFull moře ⟨Case.Ins, Number.Sg⟩ = "mořem" := by decide
example : declineFull moře ⟨Case.Nom, Number.Pl⟩ = "moře" := by decide
example : declineFull moře ⟨Case.Gen, Number.Pl⟩ = "moří" := by decide

/-! ## Test: STAVENI Paradigm (Neuter -í Invariant)
    Source: GF ResCze.gf lines 410-420
-/

def stavení := declSTAVENI "stavení"

-- Maximally invariant: almost everything = "stavení"
example : declineFull stavení ⟨Case.Nom, Number.Sg⟩ = "stavení" := by decide
example : declineFull stavení ⟨Case.Gen, Number.Sg⟩ = "stavení" := by decide
example : declineFull stavení ⟨Case.Ins, Number.Sg⟩ = "stavením" := by decide
example : declineFull stavení ⟨Case.Nom, Number.Pl⟩ = "stavení" := by decide
example : declineFull stavení ⟨Case.Dat, Number.Pl⟩ = "stavením" := by decide
example : declineFull stavení ⟨Case.Loc, Number.Pl⟩ = "staveních" := by decide
example : declineFull stavení ⟨Case.Ins, Number.Pl⟩ = "staveními" := by decide

/-! ## Known Failing Tests (Documented for Future Fixing)

These tests WOULD fail if uncommented. They document real bugs:
-/

-- Issue #1: "pes" genitive should be "psa" not "pese"
-- Root cause: "pes" has an irregular stem alternation (pe-s → p-s-a)
-- that isn't captured by dropFleetingE (which only handles ek/ec/en).
-- Fix: either expand dropFleetingE or handle "pes" as irregular.
-- example : declineFull (declMUZ "pes") ⟨Case.Gen, Number.Sg⟩ = "psa" := by decide

-- Issue #2: "okno" gen pl should be "oken" not "okn"
-- Root cause: Czech inserts epenthetic 'e' to break consonant clusters.
-- The bare stem "okn" is phonotactically invalid; needs "oken".
-- Fix: add epenthesis rule for consonant clusters in plural gen.
-- example : declineFull (declMESTO "okno") ⟨Case.Gen, Number.Pl⟩ = "oken" := by decide

end Mettapedia.Languages.GF.Czech.Tests
