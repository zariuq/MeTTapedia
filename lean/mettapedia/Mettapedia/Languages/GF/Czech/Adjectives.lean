/-
# Czech Adjective Paradigms

Full adjective inflection ported from GF Resource Grammar Library.
Czech adjectives inflect for Gender x Number x Case = 56 theoretical slots,
but heavy syncretism reduces this to ~15 distinct forms.

## Source
Ported from: ~/claude/gf-rgl/src/czech/ResCze.gf (lines 426-547)

## Paradigms Implemented
1. **mladyAdjForms** (mladý) - Hard declension (-ý)
2. **jarniAdjForms** (jarní) - Soft declension (-í)
3. **otcuvAdjForms** (otcův) - Masculine possessive (-ův)
4. **matcinAdjForms** (matčin) - Feminine possessive (-in)
5. **invarAdjForms** - Invariable (all forms identical)
-/

import Mettapedia.Languages.GF.Czech.Morphology
import Mettapedia.Languages.GF.Czech.Declensions

namespace Mettapedia.Languages.GF.Czech.Adjectives

open Mettapedia.Languages.GF.Czech
open Declensions  -- for addI, strEndsWith, strDropEnd

/-! ## Adjective Forms Record

15 named fields covering all distinct adjective forms.
The dispatch function maps these to the full 56-slot table.
Syncretism patterns documented in field comments.
-/

/-- Named adjective forms (15 distinct slots).
    Comments show which 56-slot positions map to each field. -/
structure AdjForms where
  msnom : String  -- Sg Nom/Voc Masc; Sg Acc MascInanim
  fsnom : String  -- Sg Nom/Voc Fem; Pl Nom/Acc/Voc Neutr
  nsnom : String  -- Sg Nom/Acc/Voc Neutr
  msgen : String  -- Sg Gen Masc/Neutr; Sg Acc MascAnim
  fsgen : String  -- Sg Gen Fem; Pl Acc Masc/Fem
  msdat : String  -- Sg Dat Masc/Neutr
  fsdat : String  -- Sg Dat/Loc Fem
  fsacc : String  -- Sg Acc Fem
  msloc : String  -- Sg Loc Masc/Neutr
  msins : String  -- Sg Ins Masc/Neutr; Pl Dat (all genders)
  fsins : String  -- Sg Ins Fem
  mpnom : String  -- Pl Nom/Voc MascAnim
  fpnom : String  -- Pl Nom/Voc MascInanim/Fem
  pgen  : String  -- Pl Gen/Loc (all genders)
  pins  : String  -- Pl Ins (all genders)
  deriving DecidableEq, Repr

/-! ## Phonological Helper -/

/-- Masculine animate plural nominative for hard adjectives.
    Handles: -ck -> -cti, -sk -> -sti, else palatalize via addI + long i.
    Source: GF ResCze.gf lines 63-67 -/
def addAdjI (stem : String) : String :=
  if strEndsWith stem "ck" then strDropEnd stem 2 ++ "čtí"
  else if strEndsWith stem "sk" then strDropEnd stem 2 ++ "ští"
  else
    -- addI gives e.g. "mladi", drop last char and add long "í"
    let withI := addI stem
    strDropEnd withI 1 ++ "í"

/-! ## Paradigm 1: mladyAdjForms (Hard Declension)

Pattern: adjectives ending in -ý (mladý, velký, nový, starý)
Source: GF ResCze.gf lines 495-509
-/

/-- Hard adjective paradigm (-y ending) -/
def mladyAdjForms (lemma : String) : AdjForms :=
  let stem := strDropEnd lemma 1  -- drop -y
  { msnom := stem ++ "ý"
  , fsnom := stem ++ "á"
  , nsnom := stem ++ "é"    -- also fsgen, fsdat, fpnom
  , msgen := stem ++ "ého"
  , fsgen := stem ++ "é"
  , msdat := stem ++ "ému"
  , fsdat := stem ++ "é"
  , fsacc := stem ++ "ou"   -- also fsins
  , msloc := stem ++ "ém"
  , msins := stem ++ "ým"   -- also pdat
  , fsins := stem ++ "ou"
  , mpnom := addAdjI stem
  , fpnom := stem ++ "é"
  , pgen  := stem ++ "ých"
  , pins  := stem ++ "ými" }

/-! ## Paradigm 2: jarniAdjForms (Soft Declension)

Pattern: adjectives ending in -í (jarní, poslední, letní)
Very high syncretism: most forms = lemma.
Source: GF ResCze.gf lines 513-523
-/

/-- Soft adjective paradigm (-i ending) -/
def jarniAdjForms (lemma : String) : AdjForms :=
  { msnom := lemma
  , fsnom := lemma
  , nsnom := lemma
  , msgen := lemma ++ "ho"
  , fsgen := lemma       -- also fsacc, fsins, mpnom, fpnom
  , msdat := lemma ++ "mu"
  , fsdat := lemma
  , fsacc := lemma
  , msloc := lemma ++ "m"  -- also msins
  , msins := lemma ++ "m"
  , fsins := lemma
  , mpnom := lemma
  , fpnom := lemma
  , pgen  := lemma ++ "ch"
  , pins  := lemma ++ "mi" }

/-! ## Paradigm 3: matcinAdjForms (Feminine Possessive)

Pattern: adjectives ending in -in (matčin, babiččin)
Source: GF ResCze.gf lines 534-547
-/

/-- Feminine possessive adjective paradigm (-in ending) -/
def matcinAdjForms (stem : String) : AdjForms :=
  { msnom := stem
  , fsnom := stem ++ "a"    -- also msgen
  , nsnom := stem ++ "o"
  , msgen := stem ++ "a"
  , fsgen := stem ++ "y"    -- also fpnom
  , msdat := stem ++ "u"    -- also fsacc
  , fsdat := stem ++ "ě"    -- also msloc
  , fsacc := stem ++ "u"
  , msloc := stem ++ "ě"
  , msins := stem ++ "ým"
  , fsins := stem ++ "ou"
  , mpnom := stem ++ "i"
  , fpnom := stem ++ "y"
  , pgen  := stem ++ "ých"
  , pins  := stem ++ "ými" }

/-! ## Paradigm 4: otcuvAdjForms (Masculine Possessive)

Pattern: adjectives ending in -ův (otcův, bratrův)
Derives stem by dropping -ův, adding -ov, then delegates to matcinAdjForms.
Source: GF ResCze.gf lines 527-530
-/

/-- Masculine possessive adjective paradigm (-uv ending) -/
def otcuvAdjForms (lemma : String) : AdjForms :=
  let ovStem := strDropEnd lemma 2 ++ "ov"  -- otcuv -> otcov
  let base := matcinAdjForms ovStem
  { base with msnom := lemma }  -- override msnom only

/-! ## Paradigm 5: invarAdjForms (Invariable)

All 15 fields = same string. Used for indeclinable adjectives.
Source: GF ResCze.gf lines 444-447
-/

/-- Invariable adjective (all forms identical) -/
def invarAdjForms (s : String) : AdjForms :=
  { msnom := s, fsnom := s, nsnom := s
  , msgen := s, fsgen := s, msdat := s
  , fsdat := s, fsacc := s, msloc := s
  , msins := s, fsins := s, mpnom := s
  , fpnom := s, pgen := s, pins := s }

/-! ## Smart Constructor -/

/-- Guess adjective paradigm from citation form ending -/
def guessAdjForms (s : String) : AdjForms :=
  if strEndsWith s "ý" then mladyAdjForms s
  else if strEndsWith s "í" then jarniAdjForms s
  else if strEndsWith s "ův" then otcuvAdjForms s
  else if strEndsWith s "in" then matcinAdjForms s
  else matcinAdjForms s  -- fallback

/-! ## The 56-Slot Dispatch Function

Maps 15 named AdjForms fields to the full Gender x Number x Case table.
This is the core of Czech adjective inflection.
Source: GF ResCze.gf lines 451-483
-/

/-- Decline an adjective by dispatching AdjForms fields to Gender x Number x Case.
    Covers all 56 slots (4 genders x 2 numbers x 7 cases) with heavy syncretism. -/
def adjFormsAdjective (afs : AdjForms) (p : AdjParams) : String :=
  match p.number, p.case, p.gender with
  -- === SINGULAR ===
  -- Nom/Voc Masc (any animacy): msnom
  | .Sg, .Nom, .MascAnim    => afs.msnom
  | .Sg, .Nom, .MascInanim  => afs.msnom
  | .Sg, .Voc, .MascAnim    => afs.msnom
  | .Sg, .Voc, .MascInanim  => afs.msnom
  -- Nom/Voc Fem: fsnom
  | .Sg, .Nom, .Fem         => afs.fsnom
  | .Sg, .Voc, .Fem         => afs.fsnom
  -- Nom/Acc/Voc Neutr: nsnom
  | .Sg, .Nom, .Neutr       => afs.nsnom
  | .Sg, .Acc, .Neutr       => afs.nsnom
  | .Sg, .Voc, .Neutr       => afs.nsnom
  -- Acc MascInanim = Nom (msnom)
  | .Sg, .Acc, .MascInanim  => afs.msnom
  -- Acc MascAnim = Gen (msgen) -- animate accusative!
  | .Sg, .Acc, .MascAnim    => afs.msgen
  -- Gen Masc/Neutr: msgen
  | .Sg, .Gen, .MascAnim    => afs.msgen
  | .Sg, .Gen, .MascInanim  => afs.msgen
  | .Sg, .Gen, .Neutr       => afs.msgen
  -- Gen Fem: fsgen
  | .Sg, .Gen, .Fem         => afs.fsgen
  -- Dat Masc/Neutr: msdat
  | .Sg, .Dat, .MascAnim    => afs.msdat
  | .Sg, .Dat, .MascInanim  => afs.msdat
  | .Sg, .Dat, .Neutr       => afs.msdat
  -- Dat/Loc Fem: fsdat
  | .Sg, .Dat, .Fem         => afs.fsdat
  | .Sg, .Loc, .Fem         => afs.fsdat
  -- Acc Fem: fsacc
  | .Sg, .Acc, .Fem         => afs.fsacc
  -- Loc Masc/Neutr: msloc
  | .Sg, .Loc, .MascAnim    => afs.msloc
  | .Sg, .Loc, .MascInanim  => afs.msloc
  | .Sg, .Loc, .Neutr       => afs.msloc
  -- Ins Masc/Neutr: msins
  | .Sg, .Ins, .MascAnim    => afs.msins
  | .Sg, .Ins, .MascInanim  => afs.msins
  | .Sg, .Ins, .Neutr       => afs.msins
  -- Ins Fem: fsins
  | .Sg, .Ins, .Fem         => afs.fsins
  -- === PLURAL ===
  -- Nom/Voc MascAnim: mpnom
  | .Pl, .Nom, .MascAnim    => afs.mpnom
  | .Pl, .Voc, .MascAnim    => afs.mpnom
  -- Nom/Voc MascInanim/Fem: fpnom
  | .Pl, .Nom, .MascInanim  => afs.fpnom
  | .Pl, .Nom, .Fem         => afs.fpnom
  | .Pl, .Voc, .MascInanim  => afs.fpnom
  | .Pl, .Voc, .Fem         => afs.fpnom
  -- Nom/Acc/Voc Neutr: fsnom (yes, plural neuter nom = sg fem nom)
  | .Pl, .Nom, .Neutr       => afs.fsnom
  | .Pl, .Acc, .Neutr       => afs.fsnom
  | .Pl, .Voc, .Neutr       => afs.fsnom
  -- Acc Masc/Fem: fsgen
  | .Pl, .Acc, .MascAnim    => afs.fsgen
  | .Pl, .Acc, .MascInanim  => afs.fsgen
  | .Pl, .Acc, .Fem         => afs.fsgen
  -- Dat (all genders): msins
  | .Pl, .Dat, .MascAnim    => afs.msins
  | .Pl, .Dat, .MascInanim  => afs.msins
  | .Pl, .Dat, .Fem         => afs.msins
  | .Pl, .Dat, .Neutr       => afs.msins
  -- Gen/Loc (all genders): pgen
  | .Pl, .Gen, .MascAnim    => afs.pgen
  | .Pl, .Gen, .MascInanim  => afs.pgen
  | .Pl, .Gen, .Fem         => afs.pgen
  | .Pl, .Gen, .Neutr       => afs.pgen
  | .Pl, .Loc, .MascAnim    => afs.pgen
  | .Pl, .Loc, .MascInanim  => afs.pgen
  | .Pl, .Loc, .Fem         => afs.pgen
  | .Pl, .Loc, .Neutr       => afs.pgen
  -- Ins (all genders): pins
  | .Pl, .Ins, .MascAnim    => afs.pins
  | .Pl, .Ins, .MascInanim  => afs.pins
  | .Pl, .Ins, .Fem         => afs.pins
  | .Pl, .Ins, .Neutr       => afs.pins

/-! ## Convenience Functions -/

/-- Decline an adjective given its citation form and parameters -/
def declineAdj (lemma : String) (p : AdjParams) : String :=
  adjFormsAdjective (guessAdjForms lemma) p

/-- Count distinct forms in an adjective's paradigm -/
def adjDistinctForms (afs : AdjForms) : List String :=
  let allInflected := AdjParams.allForms.map (adjFormsAdjective afs)
  allInflected.eraseDups

/-- Count distinct adjective forms (numeric) -/
def countAdjDistinctForms (afs : AdjForms) : Nat :=
  adjDistinctForms afs |>.length

end Mettapedia.Languages.GF.Czech.Adjectives
