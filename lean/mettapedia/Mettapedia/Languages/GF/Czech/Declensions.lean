/-
# Czech Declension Paradigms

Full declension paradigms ported from GF Resource Grammar Library.
These are the core patterns that cover most regular Czech nouns.

## Source
Ported from: ~/claude/gf-rgl/src/czech/ResCze.gf (lines 181-296)
Author: Aarne Ranta (March 2020)
Reference: J. Naughton, Czech: an Essential Grammar, Routledge 2005

## Paradigms Implemented
1. **declPAN** (pán) - Masculine animate hard: pán → pána, pánovi, páni, ...
2. **declHRAD** (hrad) - Masculine inanimate hard: hrad → hradu, hradě, ...
3. **declZENA** (žena) - Feminine: žena → ženy, ženě, ženou, ...
4. **declMESTO** (město) - Neuter: město → města, městu, ...
5. **declMUZ** (muž) - Masculine animate soft: muž → muže, muži, ...
-/

import Mettapedia.Languages.GF.Czech.Morphology
import Mettapedia.Languages.GF.Concrete

namespace Mettapedia.Languages.GF.Czech.Declensions

open Mettapedia.Languages.GF.Czech
open Concrete.Morphophonology

/-! ## Phonological Operations

Operations specific to Czech declensions beyond basic Morphophonology.
All use kernel-reducible string operations for provability.
-/

/-- Fleeting 'e' deletion: drops 'e' before final k/c/n in some contexts
    Examples: pes → psa, otec → otce -/
def dropFleetingE (s : String) : String :=
  if strEndsWith s "ek" then strDropEnd s 2 ++ "k"
  else if strEndsWith s "ec" then strDropEnd s 2 ++ "c"
  else if strEndsWith s "en" then strDropEnd s 2 ++ "n"
  else if strEndsWith s "eň" then strDropEnd s 2 ++ "n"
  else s

/-- Palatalization for -i endings: k→c, h→z, ch→š, r→ř
    Used in animate masculine plural nominative -/
def addI (stem : String) : String :=
  if strEndsWith stem "k" then
    strDropEnd stem 1 ++ "ci"
  else if strEndsWith stem "h" then
    strDropEnd stem 1 ++ "zi"
  else if strEndsWith stem "ch" then
    strDropEnd stem 2 ++ "ši"
  else if strEndsWith stem "r" then
    strDropEnd stem 1 ++ "ři"
  else
    stem ++ "i"

/-- Locative -ech with palatalization -/
def addEch (stem : String) : String :=
  if strEndsWith stem "k" then
    strDropEnd stem 1 ++ "cích"
  else if strEndsWith stem "h" || strEndsWith stem "g" then
    strDropEnd stem 1 ++ "zích"
  else if strEndsWith stem "ch" then
    strDropEnd stem 2 ++ "ších"
  else
    stem ++ "ech"

/-- Dative/Locative -ě with palatalization for feminine nouns -/
def addE (stem : String) : String :=
  if strEndsWith stem "k" then
    strDropEnd stem 1 ++ "ce"
  else if strEndsWith stem "g" || strEndsWith stem "h" then
    strDropEnd stem 1 ++ "ze"
  else if strEndsWith stem "ch" then
    strDropEnd stem 2 ++ "še"
  else if strEndsWith stem "r" then
    strDropEnd stem 1 ++ "ře"
  else
    stem ++ "ě"

/-! ## Paradigm 1: declPAN (Masculine Animate Hard)

Examples: pán (gentleman), kluk (boy), doktor (doctor)
Features:
- Singular vocative: vowel shortening + -e
- Plural nominative: -i with palatalization
- Plural genitive: -ů
-/

/-- Create noun following pán paradigm -/
def declPAN (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.MascAnim
  , declension := DeclensionType.pan }

/-- Decline a pán-type noun -/
def declinePAN (lemma : String) (params : CzechParams) : String :=
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => lemma ++ "a"
  | Number.Sg, Case.Dat => lemma ++ "ovi"
  | Number.Sg, Case.Acc => lemma ++ "a"
  | Number.Sg, Case.Voc => Concrete.Morphophonology.shortenLastVowel lemma ++ "e"
  | Number.Sg, Case.Loc => lemma ++ "ovi"
  | Number.Sg, Case.Ins => lemma ++ "em"
  -- Plural
  | Number.Pl, Case.Nom => addI lemma
  | Number.Pl, Case.Gen => lemma ++ "ů"
  | Number.Pl, Case.Dat => lemma ++ "ům"
  | Number.Pl, Case.Acc => lemma ++ "y"
  | Number.Pl, Case.Voc => addI lemma  -- Same as Nom
  | Number.Pl, Case.Loc => addEch lemma
  | Number.Pl, Case.Ins => lemma ++ "y"

/-! ## Paradigm 2: declHRAD (Masculine Inanimate Hard)

Examples: hrad (castle), dům (house), stůl (table)
Features:
- Nominative = Accusative (inanimate)
- Fleeting 'e' in some forms
- Singular locative: -u (or -ě with palatalization)
-/

/-- Create noun following hrad paradigm -/
def declHRAD (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.MascInanim
  , declension := DeclensionType.hrad }

/-- Decline a hrad-type noun -/
def declineHRAD (lemma : String) (params : CzechParams) : String :=
  let stem := dropFleetingE lemma
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => stem ++ "u"
  | Number.Sg, Case.Dat => stem ++ "u"
  | Number.Sg, Case.Acc => lemma  -- Inanimate: Acc = Nom
  | Number.Sg, Case.Voc => stem ++ "e"
  | Number.Sg, Case.Loc => stem ++ "u"  -- Sometimes -ě
  | Number.Sg, Case.Ins => stem ++ "em"
  -- Plural
  | Number.Pl, Case.Nom => stem ++ "y"
  | Number.Pl, Case.Gen => stem ++ "ů"
  | Number.Pl, Case.Dat => stem ++ "ům"
  | Number.Pl, Case.Acc => stem ++ "y"
  | Number.Pl, Case.Voc => stem ++ "y"
  | Number.Pl, Case.Loc => addEch stem
  | Number.Pl, Case.Ins => stem ++ "y"

/-! ## Paradigm 3: declZENA (Feminine)

Examples: žena (woman), kniha (book), škola (school)
Features:
- Stems in -a
- Dative/Locative singular: -ě with palatalization
- Plural genitive = stem (žen, not *žena)
- Instrumental singular: -ou
-/

/-- Create noun following žena paradigm -/
def declZENA (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.Fem
  , declension := DeclensionType.zena }

/-- Decline a žena-type noun -/
def declineZENA (lemma : String) (params : CzechParams) : String :=
  let stem := if strEndsWith lemma "a" then strDropEnd lemma 1 else lemma
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => stem ++ "y"
  | Number.Sg, Case.Dat => addE stem
  | Number.Sg, Case.Acc => stem ++ "u"
  | Number.Sg, Case.Voc => Concrete.Morphophonology.shortenLastVowel stem ++ "o"
  | Number.Sg, Case.Loc => addE stem  -- Same as Dat
  | Number.Sg, Case.Ins => stem ++ "ou"
  -- Plural
  | Number.Pl, Case.Nom => stem ++ "y"
  | Number.Pl, Case.Gen => stem  -- žena → žen (no ending)
  | Number.Pl, Case.Dat => stem ++ "ám"
  | Number.Pl, Case.Acc => stem ++ "y"
  | Number.Pl, Case.Voc => stem ++ "y"
  | Number.Pl, Case.Loc => stem ++ "ách"
  | Number.Pl, Case.Ins => stem ++ "ami"

/-! ## Paradigm 4: declMESTO (Neuter)

Examples: město (city), okno (window), auto (car)
Features:
- Stems in -o
- Nominative = Accusative = Vocative (neuter pattern)
- Plural nominative: -a
- Plural genitive = stem
-/

/-- Create noun following město paradigm -/
def declMESTO (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.Neutr
  , declension := DeclensionType.mesto }

/-- Decline a město-type noun -/
def declineMESTO (lemma : String) (params : CzechParams) : String :=
  let stem := if strEndsWith lemma "o" then strDropEnd lemma 1 else lemma
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => stem ++ "a"
  | Number.Sg, Case.Dat => stem ++ "u"
  | Number.Sg, Case.Acc => lemma  -- Neuter: Acc = Nom
  | Number.Sg, Case.Voc => lemma  -- Neuter: Voc = Nom
  | Number.Sg, Case.Loc => stem ++ "u"  -- Sometimes -ě
  | Number.Sg, Case.Ins => stem ++ "em"
  -- Plural
  | Number.Pl, Case.Nom => stem ++ "a"
  | Number.Pl, Case.Gen => stem  -- město → měst (no ending)
  | Number.Pl, Case.Dat => stem ++ "ům"
  | Number.Pl, Case.Acc => stem ++ "a"  -- Neuter: Acc = Nom
  | Number.Pl, Case.Voc => stem ++ "a"  -- Neuter: Voc = Nom
  | Number.Pl, Case.Loc => stem ++ "ech"
  | Number.Pl, Case.Ins => stem ++ "y"

/-! ## Paradigm 5: declMUZ (Masculine Animate Soft)

Examples: muž (man), učitel (teacher), stroj (machine)
Features:
- Soft consonant stems
- Genitive/Accusative singular: -e (not -a like hard)
- Dative/Locative singular: -i (not -ovi like hard)
- Plural forms mostly -i
-/

/-- Create noun following muž paradigm -/
def declMUZ (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.MascAnim
  , declension := DeclensionType.muz }

/-- Decline a muž-type noun -/
def declineMUZ (lemma : String) (params : CzechParams) : String :=
  let stem := dropFleetingE lemma
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => stem ++ "e"
  | Number.Sg, Case.Dat => stem ++ "i"  -- Or sometimes -ovi
  | Number.Sg, Case.Acc => stem ++ "e"
  | Number.Sg, Case.Voc => stem ++ "i"
  | Number.Sg, Case.Loc => stem ++ "i"  -- Or sometimes -ovi
  | Number.Sg, Case.Ins => stem ++ "em"
  -- Plural
  | Number.Pl, Case.Nom => stem ++ "i"  -- Or -ové for some nouns
  | Number.Pl, Case.Gen => stem ++ "ů"
  | Number.Pl, Case.Dat => stem ++ "ům"
  | Number.Pl, Case.Acc => stem ++ "e"
  | Number.Pl, Case.Voc => stem ++ "i"
  | Number.Pl, Case.Loc => stem ++ "ích"
  | Number.Pl, Case.Ins => stem ++ "i"

/-! ## Paradigm 6: declPREDSEDA (Masculine Animate -a)

Examples: předseda (chairman), kolega (colleague), turista (tourist)
Features:
- Stems in -a (like feminine, but masculine animate)
- Plural nominative: -ové (or -isté for -ista words)
- Vocative singular: -o
-/

/-- Create noun following předseda paradigm -/
def declPREDSEDA (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.MascAnim
  , declension := DeclensionType.predseda }

/-- Decline a předseda-type noun -/
def declinePREDSEDA (lemma : String) (params : CzechParams) : String :=
  let stem := if strEndsWith lemma "a" then strDropEnd lemma 1 else lemma
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => stem ++ "y"
  | Number.Sg, Case.Dat => stem ++ "ovi"
  | Number.Sg, Case.Acc => stem ++ "u"
  | Number.Sg, Case.Voc => stem ++ "o"
  | Number.Sg, Case.Loc => stem ++ "ovi"
  | Number.Sg, Case.Ins => stem ++ "ou"
  -- Plural (default -ové; -ista words use -isté but we use default)
  | Number.Pl, Case.Nom => stem ++ "ové"
  | Number.Pl, Case.Gen => stem ++ "ů"
  | Number.Pl, Case.Dat => stem ++ "ům"
  | Number.Pl, Case.Acc => stem ++ "y"
  | Number.Pl, Case.Voc => stem ++ "ové"  -- Pl Voc = Pl Nom
  | Number.Pl, Case.Loc => addEch stem
  | Number.Pl, Case.Ins => stem ++ "y"

/-! ## Paradigm 7: declSOUDCE (Masculine Animate -ce)

Examples: soudce (judge), průvodce (guide)
Features:
- Stems in -ce
- Many singular forms = lemma (high syncretism)
- Plural accusative = lemma (unusual)
-/

/-- Create noun following soudce paradigm -/
def declSOUDCE (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.MascAnim
  , declension := DeclensionType.soudce }

/-- Decline a soudce-type noun -/
def declineSOUDCE (lemma : String) (params : CzechParams) : String :=
  let stem := if strEndsWith lemma "e" then strDropEnd lemma 1 else lemma
  match params.number, params.case with
  -- Singular (Nom/Gen/Acc/Voc all = lemma)
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => lemma
  | Number.Sg, Case.Dat => stem ++ "i"
  | Number.Sg, Case.Acc => lemma
  | Number.Sg, Case.Voc => lemma
  | Number.Sg, Case.Loc => stem ++ "i"
  | Number.Sg, Case.Ins => stem ++ "em"
  -- Plural
  | Number.Pl, Case.Nom => stem ++ "i"
  | Number.Pl, Case.Gen => stem ++ "ů"
  | Number.Pl, Case.Dat => stem ++ "ům"
  | Number.Pl, Case.Acc => lemma
  | Number.Pl, Case.Voc => stem ++ "i"  -- Pl Voc = Pl Nom
  | Number.Pl, Case.Loc => stem ++ "ích"
  | Number.Pl, Case.Ins => stem ++ "i"

/-! ## Paradigm 8: declSTROJ (Masculine Inanimate Soft)

Examples: stroj (machine), počítač (computer)
Features:
- Inanimate: Nom = Acc
- Soft consonant stems
- Dat/Voc/Loc all -i in singular
-/

/-- Create noun following stroj paradigm -/
def declSTROJ (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.MascInanim
  , declension := DeclensionType.stroj }

/-- Decline a stroj-type noun -/
def declineSTROJ (lemma : String) (params : CzechParams) : String :=
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => lemma ++ "e"
  | Number.Sg, Case.Dat => lemma ++ "i"
  | Number.Sg, Case.Acc => lemma  -- Inanimate: Acc = Nom
  | Number.Sg, Case.Voc => lemma ++ "i"
  | Number.Sg, Case.Loc => lemma ++ "i"
  | Number.Sg, Case.Ins => lemma ++ "em"
  -- Plural
  | Number.Pl, Case.Nom => lemma ++ "e"
  | Number.Pl, Case.Gen => lemma ++ "ů"
  | Number.Pl, Case.Dat => lemma ++ "ům"
  | Number.Pl, Case.Acc => lemma ++ "e"
  | Number.Pl, Case.Voc => lemma ++ "e"  -- Pl Voc = Pl Nom
  | Number.Pl, Case.Loc => lemma ++ "ích"
  | Number.Pl, Case.Ins => lemma ++ "i"

/-! ## Phonological Helper: shortFemPlGen

Feminine plural genitive shortening for -e stems.
Source: GF ResCze.gf line 85-90
-/

/-- Feminine plural genitive shortening -/
def shortFemPlGen (lemma : String) : String :=
  if strEndsWith lemma "ice" then strDropEnd lemma 1      -- ulice → ulic
  else if strEndsWith lemma "yně" then strDropEnd lemma 1  -- koleg-yně → koleg-yň
  else if strEndsWith lemma "e" then strDropEnd lemma 1 ++ "í"  -- růže → růží
  else lemma

/-! ## Paradigm 9: declRUZE (Feminine Soft -e)

Examples: růže (rose), ulice (street), chvíle (moment)
Features:
- Stems in -e
- Sg Nom/Gen/Voc = lemma (high syncretism)
- Dat/Acc/Loc all -i in singular
- Special plural genitive (shortFemPlGen)
-/

/-- Create noun following růže paradigm -/
def declRUZE (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.Fem
  , declension := DeclensionType.ruze }

/-- Decline a růže-type noun -/
def declineRUZE (lemma : String) (params : CzechParams) : String :=
  let stem := if strEndsWith lemma "e" then strDropEnd lemma 1 else lemma
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => lemma
  | Number.Sg, Case.Dat => stem ++ "i"
  | Number.Sg, Case.Acc => stem ++ "i"
  | Number.Sg, Case.Voc => lemma
  | Number.Sg, Case.Loc => stem ++ "i"
  | Number.Sg, Case.Ins => stem ++ "í"
  -- Plural
  | Number.Pl, Case.Nom => lemma
  | Number.Pl, Case.Gen => shortFemPlGen lemma
  | Number.Pl, Case.Dat => stem ++ "ím"
  | Number.Pl, Case.Acc => lemma
  | Number.Pl, Case.Voc => lemma  -- Pl Voc = Pl Nom
  | Number.Pl, Case.Loc => stem ++ "ích"
  | Number.Pl, Case.Ins => stem ++ "emi"

/-! ## Paradigm 10: declPISEN (Feminine Soft Consonant)

Examples: píseň (song), báseň (poem)
Features:
- Fleeting 'e' in stem (píseň → písn-)
- Nominative/Accusative = lemma
- Uses -ě endings (gen sg, nom/acc pl)
-/

/-- Create noun following píseň paradigm -/
def declPISEN (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.Fem
  , declension := DeclensionType.pisen }

/-- Decline a píseň-type noun -/
def declinePISEN (lemma : String) (params : CzechParams) : String :=
  let stem := dropFleetingE lemma
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => stem ++ "ě"
  | Number.Sg, Case.Dat => stem ++ "i"
  | Number.Sg, Case.Acc => lemma
  | Number.Sg, Case.Voc => stem ++ "i"
  | Number.Sg, Case.Loc => stem ++ "i"
  | Number.Sg, Case.Ins => stem ++ "í"
  -- Plural
  | Number.Pl, Case.Nom => stem ++ "ě"
  | Number.Pl, Case.Gen => stem ++ "í"
  | Number.Pl, Case.Dat => stem ++ "ím"
  | Number.Pl, Case.Acc => stem ++ "ě"
  | Number.Pl, Case.Voc => stem ++ "ě"  -- Pl Voc = Pl Nom
  | Number.Pl, Case.Loc => stem ++ "ích"
  | Number.Pl, Case.Ins => stem ++ "ěmi"

/-! ## Paradigm 11: declKOST (Feminine -ost)

Examples: kost (bone), radost (joy), nemoc (disease)
Features:
- Gen/Dat/Voc/Loc singular all -i
- Very high syncretism
- Plural instrumental: -mi (not -ami)
-/

/-- Create noun following kost paradigm -/
def declKOST (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.Fem
  , declension := DeclensionType.kost }

/-- Decline a kost-type noun -/
def declineKOST (lemma : String) (params : CzechParams) : String :=
  match params.number, params.case with
  -- Singular
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => lemma ++ "i"
  | Number.Sg, Case.Dat => lemma ++ "i"
  | Number.Sg, Case.Acc => lemma
  | Number.Sg, Case.Voc => lemma ++ "i"
  | Number.Sg, Case.Loc => lemma ++ "i"
  | Number.Sg, Case.Ins => lemma ++ "í"
  -- Plural
  | Number.Pl, Case.Nom => lemma ++ "i"
  | Number.Pl, Case.Gen => lemma ++ "í"
  | Number.Pl, Case.Dat => lemma ++ "em"
  | Number.Pl, Case.Acc => lemma ++ "i"
  | Number.Pl, Case.Voc => lemma ++ "i"  -- Pl Voc = Pl Nom
  | Number.Pl, Case.Loc => lemma ++ "ech"
  | Number.Pl, Case.Ins => lemma ++ "mi"

/-! ## Paradigm 12: declKURE (Neuter, -e stem with -ete genitive)

Examples: kuře (chicken), zvíře (animal), dítě (child)
Features:
- Singular gen: -ete (extended stem)
- Plural: -ata paradigm (unique among Czech neuters)
- Neuter: Nom = Acc = Voc in singular
-/

/-- Create noun following kuře paradigm -/
def declKURE (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.Neutr
  , declension := DeclensionType.kure }

/-- Decline a kuře-type noun -/
def declineKURE (lemma : String) (params : CzechParams) : String :=
  let stem := if strEndsWith lemma "e" then strDropEnd lemma 1 else lemma
  match params.number, params.case with
  -- Singular (Nom/Acc/Voc = lemma)
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => stem ++ "ete"
  | Number.Sg, Case.Dat => stem ++ "eti"
  | Number.Sg, Case.Acc => lemma
  | Number.Sg, Case.Voc => lemma
  | Number.Sg, Case.Loc => stem ++ "eti"
  | Number.Sg, Case.Ins => stem ++ "etem"
  -- Plural (-ata paradigm)
  | Number.Pl, Case.Nom => stem ++ "ata"
  | Number.Pl, Case.Gen => stem ++ "at"
  | Number.Pl, Case.Dat => stem ++ "atům"
  | Number.Pl, Case.Acc => stem ++ "ata"
  | Number.Pl, Case.Voc => stem ++ "ata"  -- Pl Voc = Pl Nom
  | Number.Pl, Case.Loc => stem ++ "atech"
  | Number.Pl, Case.Ins => stem ++ "aty"

/-! ## Paradigm 13: declMORE (Neuter Soft, ending in e)

Examples: moře (sea), pole (field), srdce (heart)
Features:
- Sg Nom/Gen/Acc/Voc = lemma (very high syncretism)
- Pl Nom/Acc = lemma
- Distinct from kuře: no ete/ata pattern
-/

/-- Create noun following moře paradigm -/
def declMORE (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.Neutr
  , declension := DeclensionType.more }

/-- Decline a moře-type noun -/
def declineMORE (lemma : String) (params : CzechParams) : String :=
  let stem := if strEndsWith lemma "e" then strDropEnd lemma 1 else lemma
  match params.number, params.case with
  -- Singular (Nom/Gen/Acc/Voc = lemma)
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => lemma
  | Number.Sg, Case.Dat => stem ++ "i"
  | Number.Sg, Case.Acc => lemma
  | Number.Sg, Case.Voc => lemma
  | Number.Sg, Case.Loc => stem ++ "i"
  | Number.Sg, Case.Ins => stem ++ "em"
  -- Plural
  | Number.Pl, Case.Nom => lemma
  | Number.Pl, Case.Gen => stem ++ "í"
  | Number.Pl, Case.Dat => stem ++ "ím"
  | Number.Pl, Case.Acc => lemma
  | Number.Pl, Case.Voc => lemma  -- Pl Voc = Pl Nom
  | Number.Pl, Case.Loc => stem ++ "ích"
  | Number.Pl, Case.Ins => stem ++ "i"

/-! ## Paradigm 14: declSTAVENI (Neuter -í Invariant)

Examples: stavení (building), náměstí (square), nádraží (station)
Features:
- Maximally invariant: most forms = lemma
- Only Ins.Sg, Dat.Pl, Loc.Pl, Ins.Pl differ
-/

/-- Create noun following stavení paradigm -/
def declSTAVENI (lemma : String) : CzechNoun :=
  { lemma := lemma
  , gender := Gender.Neutr
  , declension := DeclensionType.staveni }

/-- Decline a stavení-type noun -/
def declineSTAVENI (lemma : String) (params : CzechParams) : String :=
  match params.number, params.case with
  -- Singular (almost all = lemma)
  | Number.Sg, Case.Nom => lemma
  | Number.Sg, Case.Gen => lemma
  | Number.Sg, Case.Dat => lemma
  | Number.Sg, Case.Acc => lemma
  | Number.Sg, Case.Voc => lemma
  | Number.Sg, Case.Loc => lemma
  | Number.Sg, Case.Ins => lemma ++ "m"
  -- Plural (mostly lemma)
  | Number.Pl, Case.Nom => lemma
  | Number.Pl, Case.Gen => lemma
  | Number.Pl, Case.Dat => lemma ++ "m"
  | Number.Pl, Case.Acc => lemma
  | Number.Pl, Case.Voc => lemma
  | Number.Pl, Case.Loc => lemma ++ "ch"
  | Number.Pl, Case.Ins => lemma ++ "mi"

/-! ## Integration with Main Decline Function -/

/-- Full declension using proper paradigms.
    Declension type uniquely determines paradigm (no gender dispatch needed).
    All 14 paradigms implemented (13 regular + irregular fallback). -/
def declineFull (n : CzechNoun) (params : CzechParams) : String :=
  match n.declension with
  | .pan      => declinePAN n.lemma params
  | .predseda => declinePREDSEDA n.lemma params
  | .soudce   => declineSOUDCE n.lemma params
  | .hrad     => declineHRAD n.lemma params
  | .muz      => declineMUZ n.lemma params
  | .stroj    => declineSTROJ n.lemma params
  | .zena     => declineZENA n.lemma params
  | .ruze     => declineRUZE n.lemma params
  | .pisen    => declinePISEN n.lemma params
  | .kost     => declineKOST n.lemma params
  | .mesto    => declineMESTO n.lemma params
  | .kure     => declineKURE n.lemma params
  | .more     => declineMORE n.lemma params
  | .staveni  => declineSTAVENI n.lemma params
  | .irregular => n.lemma

/-! ## Inflection Table Construction (using declineFull)

These utilities now use declineFull for correct paradigm-based declension.
-/

/-- Build complete inflection table for a Czech noun using full paradigms -/
def toInflectionTable (n : CzechNoun) : Concrete.InflectionTable CzechParams :=
  { table := fun params => declineFull n params }

/-! ## Syncretism Analysis (using declineFull)

Count distinct forms and detect syncretism using correct paradigms.
-/

/-- Count distinct forms in a noun's paradigm using declineFull -/
def distinctForms (n : CzechNoun) : List String :=
  let allInflected := CzechParams.allForms.map (declineFull n)
  allInflected.eraseDups

/-- Count distinct forms (numeric version) -/
def countDistinctForms (n : CzechNoun) : Nat :=
  distinctForms n |>.length

/-- Check if a noun exhibits syncretism (fewer distinct forms than slots) -/
def hasSyncretism (n : CzechNoun) : Bool :=
  (distinctForms n).length < CzechParams.allForms.length

end Mettapedia.Languages.GF.Czech.Declensions
