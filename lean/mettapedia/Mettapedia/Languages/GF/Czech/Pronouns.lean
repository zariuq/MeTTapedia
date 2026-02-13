/-
# Czech Pronouns

Personal, possessive, demonstrative, and interrogative pronouns
ported from GF Resource Grammar Library.

## Source
Ported from: ~/claude/gf-rgl/src/czech/ResCze.gf (lines 625-846)

## Pronouns Implemented
1. **personalPron** - 8 personal pronouns (ja/ty/on/ona/ono/my/vy/oni)
2. **possessivePron** - 7 possessive pronoun paradigms (muj/tvuj/nas/vas/jeji/jeho/jejich)
3. **reflPossessivePron** - reflexive possessive (svuj)
4. **mkDemPronForms** - demonstrative (ten/ta/to)
5. **invarDemPronForms** - invariable demonstrative
6. **kdoForms** - interrogative "who"
7. **coForms** - interrogative "what"
-/

import Mettapedia.Languages.GF.Czech.Morphology
import Mettapedia.Languages.GF.Czech.Adjectives

namespace Mettapedia.Languages.GF.Czech.Pronouns

open Mettapedia.Languages.GF.Czech
open Adjectives

/-! ## Personal Pronoun Forms

14 fields covering all case forms including clitic and prepositional variants.
Source: GF ResCze.gf lines 625-633
-/

/-- Personal pronoun forms: full, clitic, and prepositional variants for each case -/
structure PronForms where
  nom   : String  -- full nominative (ja, ty, on)
  cnom  : String  -- pro-drop subject (empty string)
  gen   : String  -- full genitive (mne, tebe)
  cgen  : String  -- clitic genitive (me, te)
  pgen  : String  -- prepositional genitive (mne, tebe)
  acc   : String  -- full accusative
  cacc  : String  -- clitic accusative
  pacc  : String  -- prepositional accusative
  dat   : String  -- full dative
  cdat  : String  -- clitic dative (mi, ti)
  pdat  : String  -- prepositional dative
  loc   : String  -- locative
  ins   : String  -- instrumental
  pins  : String  -- prepositional instrumental
  agr   : Agr     -- agreement features
  deriving DecidableEq, Repr

/-! ## Demonstrative Pronoun Forms

15 fields (like AdjForms but with different fsdat and pdat behavior).
Key difference from AdjForms: fsdat = fsgen (not separate), pdat is independent (not = msins).
Source: GF ResCze.gf lines 761-772
-/

/-- Demonstrative pronoun forms (15 fields).
    Differs from AdjForms: fsdat = fsgen, pdat independent of msins. -/
structure DemPronForms where
  msnom : String  -- Sg Nom Masc
  fsnom : String  -- Sg Nom Fem
  nsnom : String  -- Sg Nom Neutr
  msgen : String  -- Sg Gen Masc/Neutr
  fsgen : String  -- Sg Gen Fem; also fsdat for demonstratives
  msdat : String  -- Sg Dat Masc/Neutr
  fsacc : String  -- Sg Acc Fem
  msloc : String  -- Sg Loc Masc/Neutr
  msins : String  -- Sg Ins Masc/Neutr
  fsins : String  -- Sg Ins Fem
  mpnom : String  -- Pl Nom MascAnim
  fpnom : String  -- Pl Nom MascInanim/Fem; also Pl Acc Masc/Fem
  pgen  : String  -- Pl Gen/Loc
  pdat  : String  -- Pl Dat (NOT = msins like AdjForms)
  pins  : String  -- Pl Ins
  deriving DecidableEq, Repr

/-! ## Personal Pronouns

8-way dispatch on agreement features.
Source: GF ResCze.gf lines 635-721
-/

/-- Helper: build a PronForms with all fields set -/
private def mkPronForms (a : Agr) (nom gen cgen pgen acc cacc pacc dat cdat pdat loc ins pins : String) : PronForms :=
  { nom := nom, cnom := "", gen := gen, cgen := cgen, pgen := pgen
  , acc := acc, cacc := cacc, pacc := pacc
  , dat := dat, cdat := cdat, pdat := pdat
  , loc := loc, ins := ins, pins := pins, agr := a }

/-- Personal pronoun forms for all 8 person/number/gender combinations.
    Source: GF ResCze.gf lines 635-721 -/
def personalPron (a : Agr) : PronForms :=
  match a.number, a.person, a.gender with
  -- ja (I)
  | .Sg, .P1, _ =>
    mkPronForms a "já" "mne" "mě" "mne" "mne" "mě" "mne" "mně" "mi" "mně" "mně" "mnou" "mnou"
  -- ty (you sg)
  | .Sg, .P2, _ =>
    mkPronForms a "ty" "tebe" "tě" "tebe" "tebe" "tě" "tebe" "tobě" "ti" "tobě" "tobě" "tebou" "tebou"
  -- on (he) - masculine animate or inanimate
  | .Sg, .P3, .MascAnim | .Sg, .P3, .MascInanim =>
    mkPronForms a "on" "jeho" "ho" "něho" "jeho" "ho" "něho" "jemu" "mu" "němu" "něm" "jím" "ním"
  -- ona (she)
  | .Sg, .P3, .Fem =>
    mkPronForms a "ona" "její" "ji" "ní" "ji" "ji" "ní" "ji" "ji" "ní" "ní" "ji" "ní"
  -- ono (it)
  | .Sg, .P3, .Neutr =>
    mkPronForms a "ono" "jeho" "ho" "něho" "je" "ho" "ně" "jemu" "mu" "němu" "něm" "jím" "ním"
  -- my (we)
  | .Pl, .P1, _ =>
    mkPronForms a "my" "nás" "nás" "nás" "nás" "nás" "nás" "nám" "nám" "nám" "nás" "námi" "námi"
  -- vy (you pl)
  | .Pl, .P2, _ =>
    mkPronForms a "vy" "vás" "vás" "vás" "vás" "vás" "vás" "vám" "vám" "vám" "vás" "vámi" "vámi"
  -- oni/ony/ona (they)
  | .Pl, .P3, g =>
    let nomForm := match g with
      | .MascAnim | .MascInanim => "oni"
      | .Fem => "ony"
      | .Neutr => "ona"
    mkPronForms a nomForm "jich" "jich" "nich" "je" "je" "ně" "jim" "jim" "nim" "nich" "jimi" "nimi"

/-! ## Possessive Pronouns

Reuse adjective paradigms (mladyAdjForms, jarniAdjForms) with overrides.
Source: GF ResCze.gf lines 723-752
-/

/-- Convert AdjForms to DemPronForms (pdat defaults to msins in AdjForms) -/
def adjFormsToDemPron (af : AdjForms) : DemPronForms :=
  { msnom := af.msnom, fsnom := af.fsnom, nsnom := af.nsnom
  , msgen := af.msgen, fsgen := af.fsgen
  , msdat := af.msdat, fsacc := af.fsacc
  , msloc := af.msloc, msins := af.msins, fsins := af.fsins
  , mpnom := af.mpnom, fpnom := af.fpnom
  , pgen := af.pgen, pdat := af.msins, pins := af.pins }

/-- Helper: invariable DemPronForms (all fields = s) -/
private def invarDemPron (s : String) : DemPronForms :=
  { msnom := s, fsnom := s, nsnom := s, msgen := s, fsgen := s
  , msdat := s, fsacc := s, msloc := s, msins := s, fsins := s
  , mpnom := s, fpnom := s, pgen := s, pdat := s, pins := s }

/-- Possessive pronoun forms for each person/number combination.
    Source: GF ResCze.gf lines 723-750 -/
def possessivePron (a : Agr) : DemPronForms :=
  match a.number, a.person, a.gender with
  -- muj (my)
  | .Sg, .P1, _ =>
    let b := adjFormsToDemPron (mladyAdjForms "my")
    { b with msnom := "můj", pdat := "mým" }
  -- tvuj (your sg)
  | .Sg, .P2, _ =>
    let b := adjFormsToDemPron (mladyAdjForms "tvy")
    { b with msnom := "tvůj", pdat := "tvým" }
  -- nas (our)
  | .Pl, .P1, _ =>
    let b := adjFormsToDemPron (jarniAdjForms "naše")
    { b with msnom := "náš", fsgen := "naši", mpnom := "naši",
             fsins := "naší", pdat := "našim", msins := "našim",
             pgen := "našich", pins := "našimi" }
  -- vas (your pl)
  | .Pl, .P2, _ =>
    let b := adjFormsToDemPron (jarniAdjForms "vaše")
    { b with msnom := "váš", fsgen := "vaši", mpnom := "vaši",
             fsins := "vaší", pdat := "vašim", msins := "vašim",
             pgen := "vašich", pins := "vašimi" }
  -- jeji (her)
  | .Sg, .P3, .Fem =>
    let b := adjFormsToDemPron (jarniAdjForms "její")
    { b with pdat := "jejím" }
  -- jeho (his/its) - masculine or neuter 3rd person sg
  | .Sg, .P3, .MascAnim | .Sg, .P3, .MascInanim | .Sg, .P3, .Neutr =>
    let b := invarDemPron "jeho"
    { b with pdat := "jeho" }
  -- jejich (their)
  | .Pl, .P3, _ =>
    let b := invarDemPron "jejich"
    { b with pdat := "jejich" }

/-- Reflexive possessive pronoun "svuj".
    Source: GF ResCze.gf line 752 -/
def reflPossessivePron : DemPronForms :=
  let b := adjFormsToDemPron (mladyAdjForms "svy")
  { b with msnom := "svůj", pdat := "svým" }

/-! ## Demonstrative Pronouns

ten/ta/to paradigm and invariable.
Source: GF ResCze.gf lines 806-828
-/

/-- Demonstrative pronoun paradigm (ten/ta/to).
    Takes the stem (e.g., "t") and builds all 15 forms.
    Source: GF ResCze.gf lines 806-822 -/
def mkDemPronForms (stem : String) : DemPronForms :=
  { msnom := stem ++ "en", fsnom := stem ++ "a", nsnom := stem ++ "o"
  , msgen := stem ++ "oho", fsgen := stem ++ "é"
  , msdat := stem ++ "omu", fsacc := stem ++ "u"
  , msloc := stem ++ "om", msins := stem ++ "ím", fsins := stem ++ "ou"
  , mpnom := stem ++ "i", fpnom := stem ++ "y"
  , pgen := stem ++ "ěch", pdat := stem ++ "ěm", pins := stem ++ "ěmi" }

/-- Invariable demonstrative pronoun (all forms identical).
    Source: GF ResCze.gf lines 824-828 -/
def invarDemPronForms (s : String) : DemPronForms :=
  invarDemPron s

/-! ## Demonstrative Pronoun Dispatch

Like adjFormsAdjective, but with two key differences:
1. fsdat = fsgen (not a separate field)
2. Pl Dat = pdat (not msins)
3. Pl Acc Masc/Fem = fpnom (not fsgen)
Source: GF ResCze.gf lines 774-798
-/

/-- Dispatch DemPronForms to Gender x Number x Case.
    Differs from adjFormsAdjective in Pl Dat (uses pdat) and Pl Acc (uses fpnom). -/
def demPronFormsAdjective (dem : DemPronForms) (p : AdjParams) : String :=
  match p.number, p.case, p.gender with
  -- Plural overrides (the key differences from adjFormsAdjective)
  | .Pl, .Dat, _           => dem.pdat
  | .Pl, .Acc, .MascAnim   => dem.fpnom
  | .Pl, .Acc, .MascInanim => dem.fpnom
  | .Pl, .Acc, .Fem        => dem.fpnom
  -- Everything else: delegate to adjFormsAdjective with fsdat = fsgen
  | n, c, g =>
    let asAdj : AdjForms :=
      { msnom := dem.msnom, fsnom := dem.fsnom, nsnom := dem.nsnom
      , msgen := dem.msgen, fsgen := dem.fsgen
      , msdat := dem.msdat, fsdat := dem.fsgen
      , fsacc := dem.fsacc, msloc := dem.msloc
      , msins := dem.msins, fsins := dem.fsins
      , mpnom := dem.mpnom, fpnom := dem.fpnom
      , pgen := dem.pgen, pins := dem.pins }
    adjFormsAdjective asAdj ⟨g, n, c⟩

/-! ## Interrogative Pronouns

Simple case-dispatched forms.
Source: GF ResCze.gf lines 832-846
-/

/-- Interrogative pronoun "kdo" (who).
    Source: GF ResCze.gf lines 832-838 -/
def kdoForms (c : Case) : String :=
  match c with
  | .Nom => "kdo"
  | .Gen | .Acc | .Voc => "koho"
  | .Dat => "komu"
  | .Loc => "kom"
  | .Ins => "kým"

/-- Interrogative pronoun "co" (what).
    Source: GF ResCze.gf lines 840-846 -/
def coForms (c : Case) : String :=
  match c with
  | .Nom | .Acc | .Voc => "co"
  | .Gen => "čeho"
  | .Dat => "čemu"
  | .Loc => "čem"
  | .Ins => "čím"

end Mettapedia.Languages.GF.Czech.Pronouns
