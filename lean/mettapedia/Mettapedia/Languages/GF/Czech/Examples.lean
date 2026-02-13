/-
# Czech Declension Examples and Tests

Executable test cases demonstrating Czech noun declensions.
These verify that:
1. Paradigms produce correct Czech forms
2. Syncretism occurs (fewer distinct forms than slots)
3. Compression paradox holds (rich morphology → regular patterns)

Run tests with: `lake env lean --run Mettapedia/Languages/GF/Czech/Examples.lean`
-/

import Mettapedia.Languages.GF.Czech.Morphology
import Mettapedia.Languages.GF.Czech.Declensions

namespace Mettapedia.Languages.GF.Czech.Examples

open Mettapedia.Languages.GF.Czech
open Declensions  -- This now includes toInflectionTable, distinctForms, hasSyncretism

/-! ## Example Nouns from Each Paradigm -/

/-- pán (gentleman) - masculine animate hard -/
def pán : CzechNoun := declPAN "pán"

/-- hrad (castle) - masculine inanimate hard -/
def hrad : CzechNoun := declHRAD "hrad"

/-- žena (woman) - feminine -/
def žena : CzechNoun := declZENA "žena"

/-- město (city) - neuter -/
def město : CzechNoun := declMESTO "město"

/-- muž (man) - masculine animate soft -/
def muž : CzechNoun := declMUZ "muž"

/-! ## Test Individual Forms -/

section TestForms

-- Test pán declension
#eval declineFull pán ⟨Case.Nom, Number.Sg⟩  -- Expected: "pán"
#eval declineFull pán ⟨Case.Gen, Number.Sg⟩  -- Expected: "pána"
#eval declineFull pán ⟨Case.Nom, Number.Pl⟩  -- Expected: "páni" (with palatalization)

-- Test žena declension
#eval declineFull žena ⟨Case.Nom, Number.Sg⟩  -- Expected: "žena"
#eval declineFull žena ⟨Case.Gen, Number.Sg⟩  -- Expected: "ženy"
#eval declineFull žena ⟨Case.Gen, Number.Pl⟩  -- Expected: "žen" (no ending!)

-- Test město declension
#eval declineFull město ⟨Case.Nom, Number.Sg⟩  -- Expected: "město"
#eval declineFull město ⟨Case.Gen, Number.Sg⟩  -- Expected: "města"
#eval declineFull město ⟨Case.Nom, Number.Pl⟩  -- Expected: "města" (same as Gen.Sg!)

end TestForms

/-! ## Test Syncretism (Form Reduction)

Czech has 14 theoretical slots (7 cases × 2 numbers) but most nouns
use fewer distinct forms due to syncretism.
-/

section TestSyncretism

-- countDistinctForms now imported from Declensions
-- Test compression: 14 slots → how many distinct forms?
#eval countDistinctForms pán    -- Expected: ~10-12 (some syncretism)
#eval countDistinctForms hrad   -- Expected: ~8-10
#eval countDistinctForms žena   -- Expected: ~8-9
#eval countDistinctForms město  -- Expected: ~7-8 (high syncretism)
#eval countDistinctForms muž    -- Expected: ~9-11

-- Verify syncretism exists
#eval hasSyncretism pán    -- Expected: true
#eval hasSyncretism žena   -- Expected: true
#eval hasSyncretism město  -- Expected: true

end TestSyncretism

/-! ## Test Phonological Rules -/

section TestPhonology

-- Test vowel shortening (á→a, é→e in vocative)
#eval declineFull pán ⟨Case.Voc, Number.Sg⟩  -- Expected: "pane" (pán → pan + e)

-- Test palatalization (k→c before -i)
def kluk : CzechNoun := declPAN "kluk"
#eval declineFull kluk ⟨Case.Nom, Number.Pl⟩  -- Expected: "kluci" (not *kluki)

-- Test fleeting e (pes → psa)
def pes : CzechNoun := declMUZ "pes"
#eval declineFull pes ⟨Case.Gen, Number.Sg⟩  -- Expected: "psa" (fleeting e dropped)

end TestPhonology

/-! ## Paradigm Coverage Test -/

/-- Additional test nouns covering various patterns -/
def kniha : CzechNoun := declZENA "kniha"          -- book (feminine)
def okno : CzechNoun := declMESTO "okno"           -- window (neuter)
def stůl : CzechNoun := declHRAD "stůl"            -- table (inanimate)
def učitel : CzechNoun := declMUZ "učitel"         -- teacher (soft)

/-! ## New Paradigm Examples -/
def předseda : CzechNoun := declPREDSEDA "předseda"  -- chairman (masc animate -a)
def soudce : CzechNoun := declSOUDCE "soudce"        -- judge (masc animate -ce)
def stroj : CzechNoun := declSTROJ "stroj"            -- machine (masc inanim soft)
def růže : CzechNoun := declRUZE "růže"              -- rose (fem soft -e)
def píseň : CzechNoun := declPISEN "píseň"          -- song (fem soft consonant)
def kost : CzechNoun := declKOST "kost"              -- bone (fem -ost)
def kuře : CzechNoun := declKURE "kuře"              -- chicken (neuter -ete)
def moře : CzechNoun := declMORE "moře"              -- sea (neuter soft -e)
def stavení : CzechNoun := declSTAVENI "stavení"     -- building (neuter -í)

section CoverageTest

-- Verify all paradigms accessible
#eval declineFull kniha ⟨Case.Ins, Number.Sg⟩   -- Expected: "knihou"
#eval declineFull okno ⟨Case.Gen, Number.Pl⟩    -- Expected: "oken"
#eval declineFull stůl ⟨Case.Loc, Number.Sg⟩    -- Expected: "stolu" or "stole"
#eval declineFull učitel ⟨Case.Nom, Number.Pl⟩  -- Expected: "učitelé" or "učiteli"

end CoverageTest

/-! ## Inflection Table Test

Build complete inflection table and verify it's computable.
-/

section InflectionTableTest

-- Create inflection table for pán
def pánTable := toInflectionTable pán

-- Lookup specific forms from table
#eval pánTable.table ⟨Case.Dat, Number.Sg⟩  -- Expected: "pánovi"
#eval pánTable.table ⟨Case.Loc, Number.Pl⟩  -- Expected: "pánech" or "pánich"

end InflectionTableTest

/-! ## Summary Statistics -/

def testNouns : List CzechNoun :=
  [pán, hrad, žena, město, muž, kluk, kniha, okno,
   předseda, soudce, stroj, růže, píseň, kost, kuře, moře, stavení]

#eval testNouns.map countDistinctForms  -- Show compression for all test nouns

/-- Average compression ratio across test nouns -/
def averageCompressionRatio : Rat :=
  let distinctCounts := testNouns.map countDistinctForms
  let totalDistinct : Int := (distinctCounts.foldl (· + ·) 0 : Nat)
  let totalSlots : Int := ((14 * testNouns.length) : Nat)
  Rat.divInt totalDistinct totalSlots

#eval averageCompressionRatio  -- Expected: ~0.6-0.7 (30-40% compression)

end Mettapedia.Languages.GF.Czech.Examples
