/-
# Shared GF Helpers for README Generation

Common GF infrastructure used by all compositional README modules:
properNameNP, ppAdv, linConjNP, mkPresPos, withParenRef, etc.
-/

import Mettapedia.Languages.GF.English.Examples
import Mettapedia.Languages.GF.English.Pronouns

namespace Mettapedia.DocText.ReadmeGFHelpers

open Mettapedia.Languages.GF.English
open Mettapedia.Languages.GF.English.Nouns
open Mettapedia.Languages.GF.English.Verbs
open Mettapedia.Languages.GF.English.Adjectives
open Mettapedia.Languages.GF.English.Syntax
open Mettapedia.Languages.GF.English.Pronouns

/-- Proper name NP — legitimate literal in GF (UsePN).
    Used only for: repo names, file paths, code literals, technology names. -/
def properNameNP (name : String) (agr : Agr := .AgP3Sg .Neutr) : EnglishNP :=
  { s := fun
      | .NCase .Nom => name
      | .NCase .Gen => name ++ "'s"
      | .NPAcc => name
      | .NPNomPoss => name ++ "'s"
    agr := agr
  }

/-- Render NP coordination as a string: "X, Y and Z". -/
def conjNPStr (conj : EnglishConj) (nps : List EnglishNP) (c : NPCase) : String :=
  let strs := nps.map (·.s c)
  let pfx := if conj.s1 == "" then "" else conj.s1 ++ " "
  match strs with
  | [] => ""
  | [x] => x
  | [x, y] => pfx ++ x ++ " " ++ conj.s2 ++ " " ++ y
  | [x, y, z] => pfx ++ x ++ ", " ++ y ++ " " ++ conj.s2 ++ " " ++ z
  | [w, x, y, z] => pfx ++ w ++ ", " ++ x ++ ", " ++ y ++ " " ++ conj.s2 ++ " " ++ z
  | _ => String.intercalate ", " strs  -- fallback for 5+

/-- GF-style NP coordination: "X, Y and Z" -/
def linConjNP (conj : EnglishConj) (nps : List EnglishNP) : EnglishNP :=
  { s := conjNPStr conj nps
    agr := if conj.n == .Pl then .AgP3Pl else .AgP3Sg .Neutr }

/-- Build a PP string from prep + NP, for use with advVP -/
def ppAdv (prep : EnglishPrep) (np : EnglishNP) : String :=
  linPrepNP prep np

/-- Sentence-initial "This" (capitalized) -/
def This_Det : EnglishDet := { s := "This", n := .Sg, isDef := true }

def ensurePeriod (s : String) : String :=
  if s.endsWith "." then s else s ++ "."

/-- Present-tense positive declarative clause -/
def mkPresPos (subj : EnglishNP) (vp : EnglishVP) : String :=
  linUseCl .Pres .Simul .CPos (linPredVP subj vp)

/-- Present-tense negative declarative clause -/
def mkPresNeg (subj : EnglishNP) (vp : EnglishVP) : String :=
  linUseCl .Pres .Simul (.CNeg true) (linPredVP subj vp)

/-- Append a parenthetical reference after a generated clause.
    Not part of GF grammar — parentheticals are metalinguistic. -/
def withParenRef (clause : String) (ref : String) : String :=
  clause ++ " (see " ++ ref ++ ")"

/-- Copula "be" as EnglishVP with NP complement: produces "is/are Y".
    GF RGL: UseComp (CompNP np) with special "be" verb forms. -/
def copulaNP (complement : EnglishNP) : EnglishVP :=
  { inf := "be"
    pres := fun agr => match agr with
      | .AgP3Sg _ => "is"
      | _ => "are"
    past := "was"
    ppart := "been"
    prpart := "being"
    particle := ""
    compl := fun _ => complement.s (.NCase .Nom)
    adv := "" }

/-- Copula "be" with adjective complement: produces "is/are ADJ".
    GF RGL: UseComp (CompAP ap). -/
def copulaAdj (adj : String) : EnglishVP :=
  { inf := "be"
    pres := fun agr => match agr with
      | .AgP3Sg _ => "is"
      | _ => "are"
    past := "was"
    ppart := "been"
    prpart := "being"
    particle := ""
    compl := fun _ => adj
    adv := "" }

/-- Bare plural NP (no determiner): "systems", "premises" -/
def linMassPluralNP (cn : EnglishCN) : EnglishNP :=
  { s := fun _ => cn.s .Pl .Nom
    agr := .AgP3Pl }

/-- Present-tense negative copula clause: "X isn't Y" / "X aren't Y".
    Copula negation needs special handling (not do-support). -/
def mkPresNegCopulaNP (subj : EnglishNP) (complement : EnglishNP) : String :=
  let subjStr := subj.s (.NCase .Nom)
  let cop := match subj.agr with
    | .AgP3Sg _ => "isn't"
    | _ => "aren't"
  subjStr ++ " " ++ cop ++ " " ++ complement.s (.NCase .Nom)

/-- Present-tense negative copula with string complement: "X isn't Y" -/
def mkPresNegCopulaStr (subj : EnglishNP) (complement : String) : String :=
  let subjStr := subj.s (.NCase .Nom)
  let cop := match subj.agr with
    | .AgP3Sg _ => "isn't"
    | _ => "aren't"
  subjStr ++ " " ++ cop ++ " " ++ complement

/-- Capitalize first character of a string -/
def capitalizeFirst (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- Heading surface from singular mass NP. -/
def headingNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassNP cn).s (.NCase .Nom)

/-- Heading surface from plural mass NP. -/
def headingPlNP (cn : EnglishCN) : String :=
  capitalizeFirst <| (linMassPluralNP cn).s (.NCase .Nom)

/-- Strip terminal period from a string -/
def stripTerminalPeriod (s : String) : String :=
  match s.toList.reverse with
  | '.' :: cs => String.ofList cs.reverse
  | _ => s

end Mettapedia.DocText.ReadmeGFHelpers
