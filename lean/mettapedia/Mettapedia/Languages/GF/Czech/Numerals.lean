/-
# Czech Numerals

Numeral forms and determiner construction ported from GF Resource Grammar Library.
Czech numerals govern noun case in complex ways (NumSize system).

## Source
Ported from: ~/claude/gf-rgl/src/czech/ResCze.gf (lines 850-914)

## Numerals Implemented
1. **oneNumeral** - jeden/jedna/jedno (singular agreement)
2. **twoNumeral** - dva/dve (Num2_4 agreement)
3. **threeNumeral** - tri (Num2_4 agreement)
4. **fourNumeral** - ctyri (Num2_4 agreement)
5. **regNumeral** - 5+ pattern (Num5 agreement, forces genitive plural)
6. **invarNumeral** - invariable (sto, tisic)
-/

import Mettapedia.Languages.GF.Czech.Morphology
import Mettapedia.Languages.GF.Czech.Adjectives
import Mettapedia.Languages.GF.Czech.Pronouns

namespace Mettapedia.Languages.GF.Czech.Numerals

open Mettapedia.Languages.GF.Czech
open Adjectives Pronouns

/-! ## Numeral Forms

Singular forms only (plural forms not used for numeral determiners).
Source: GF ResCze.gf lines 851-858
-/

/-- Numeral forms: singular declension (10 fields).
    Plural forms are filled uniformly from msnom in the determiner. -/
structure NumeralForms where
  msnom : String  -- Sg Nom Masc
  fsnom : String  -- Sg Nom Fem
  nsnom : String  -- Sg Nom Neutr
  msgen : String  -- Sg Gen Masc/Neutr
  fsgen : String  -- Sg Gen Fem
  msdat : String  -- Sg Dat Masc/Neutr
  fsacc : String  -- Sg Acc Fem
  msloc : String  -- Sg Loc Masc/Neutr
  msins : String  -- Sg Ins Masc/Neutr
  fsins : String  -- Sg Ins Fem
  deriving DecidableEq, Repr

/-- Czech determiner: string dispatch (Gender x Case) + NumSize.
    Source: GF ResCze.gf lines 801-804 -/
structure Determiner where
  s    : Gender → Case → String
  size : NumSize
  deriving Inhabited

/-! ## Numeral Forms to Determiner

Converts NumeralForms to a Determiner via the adjective dispatch.
The plural fields are filled from msnom (not used in practice).
Source: GF ResCze.gf lines 860-870
-/

/-- Convert NumeralForms + NumSize to a Determiner.
    Builds a DemPronForms (plural fields = msnom), then dispatches via adjective table.
    Source: GF ResCze.gf lines 860-870 -/
def numeralFormsDeterminer (nf : NumeralForms) (size : NumSize) : Determiner :=
  let dem : DemPronForms :=
    { msnom := nf.msnom, fsnom := nf.fsnom, nsnom := nf.nsnom
    , msgen := nf.msgen, fsgen := nf.fsgen
    , msdat := nf.msdat
    , fsacc := nf.fsacc
    , msloc := nf.msloc
    , msins := nf.msins, fsins := nf.fsins
    , mpnom := nf.msnom, fpnom := nf.msnom
    , pgen := nf.msnom, pdat := nf.msnom, pins := nf.msnom }
  let asAdj : AdjForms :=
    { msnom := dem.msnom, fsnom := dem.fsnom, nsnom := dem.nsnom
    , msgen := dem.msgen, fsgen := dem.fsgen
    , msdat := dem.msdat
    , fsdat := dem.fsgen  -- fsdat = fsgen for demonstratives
    , fsacc := dem.fsacc
    , msloc := dem.msloc
    , msins := dem.msins, fsins := dem.fsins
    , mpnom := dem.mpnom, fpnom := dem.fpnom
    , pgen := dem.pgen, pins := dem.pins }
  { s := fun g c => adjFormsAdjective asAdj ⟨g, .Sg, c⟩
  , size := size }

/-! ## Lexicalized Numerals

Source: GF ResCze.gf lines 873-914
-/

/-- Numeral "jeden" (one). Num1 = singular agreement.
    Source: GF ResCze.gf line 873 -/
def oneNumeral : Determiner :=
  let forms := mkDemPronForms "jedn"
  let nf : NumeralForms :=
    { msnom := "jeden"  -- override from mkDemPronForms "jednen"
    , fsnom := forms.fsnom, nsnom := forms.nsnom
    , msgen := forms.msgen, fsgen := forms.fsgen
    , msdat := forms.msdat, fsacc := forms.fsacc
    , msloc := forms.msloc, msins := forms.msins, fsins := forms.fsins }
  numeralFormsDeterminer nf .Num1

/-- Numeral "dva" (two). Num2_4 = plural agreement.
    Source: GF ResCze.gf lines 876-882 -/
def twoNumeral : Determiner :=
  let nf : NumeralForms :=
    { msnom := "dva"
    , fsnom := "dvě", nsnom := "dvě", fsacc := "dvě"
    , msgen := "dvou", fsgen := "dvou", msloc := "dvou"
    , msdat := "dvěma", msins := "dvěma", fsins := "dvěma" }
  numeralFormsDeterminer nf .Num2_4

/-- Numeral "tri" (three). Num2_4 = plural agreement.
    Source: GF ResCze.gf lines 884-891 -/
def threeNumeral : Determiner :=
  let nf : NumeralForms :=
    { msnom := "tři", fsnom := "tři", nsnom := "tři", fsacc := "tři"
    , msgen := "tři", fsgen := "tři"
    , msdat := "třem"
    , msloc := "třech"
    , msins := "třemi", fsins := "třemi" }
  numeralFormsDeterminer nf .Num2_4

/-- Numeral "ctyri" (four). Num2_4 = plural agreement.
    Source: GF ResCze.gf lines 893-901 -/
def fourNumeral : Determiner :=
  let nf : NumeralForms :=
    { msnom := "čtyři", fsnom := "čtyři", nsnom := "čtyři", fsacc := "čtyři"
    , msgen := "čtyř", fsgen := "čtyř"
    , msdat := "čtyřem"
    , msloc := "čtyřech"
    , msins := "čtyřmi", fsins := "čtyřmi" }
  numeralFormsDeterminer nf .Num2_4

/-- Regular numeral for 5+ (e.g., pet/peti). Num5 = forces genitive plural.
    Source: GF ResCze.gf lines 904-909 -/
def regNumeral (nom oblique : String) : Determiner :=
  let nf : NumeralForms :=
    { msnom := nom, fsnom := nom, nsnom := nom
    , msgen := oblique, fsgen := oblique
    , msdat := oblique, fsacc := oblique
    , msloc := oblique
    , msins := oblique, fsins := oblique }
  numeralFormsDeterminer nf .Num5

/-- Invariable numeral (e.g., sto, tisic). All forms identical, Num5.
    Source: GF ResCze.gf lines 911-914 -/
def invarNumeral (s : String) : Determiner :=
  regNumeral s s

end Mettapedia.Languages.GF.Czech.Numerals
