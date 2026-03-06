import Mettapedia.Languages.GF.English.Linearization.Types

namespace Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Core Abstract
open English
open Syntax Pronouns Relatives
open Nouns Verbs Adjectives
def copulaVP (renderComp : Agr → String) : EnglishVP :=
  { inf := "be"
    pres := fun agr => match agr with
      | .AgP3Sg _ => "is"
      | _ => "are"
    past := "was"
    ppart := "been"
    prpart := "being"
    particle := ""
    compl := renderComp
    adv := "" }

def addCompPrep (prep : String) (s : String) : String :=
  if prep == "" then s else prep ++ " " ++ s

def vpCompSurface (vp : EnglishVP) : String :=
  joinWords [vp.inf, vp.particle, vp.compl (.AgP3Sg .Neutr), vp.adv]

def applyV3Slash (v3 : EnglishV3Frame) (filled : String) (missingPrep : String) : EnglishVPSlash :=
  let base : EnglishVP :=
    { (predV v3.verb) with compl := fun _ => filled }
  { base with c2 := missingPrep }

def applyV2CompSlash (v2c : EnglishV2CompFrame) (compText : String) : EnglishVPSlash :=
  let compWithPrep := addCompPrep v2c.compPrep compText
  let base : EnglishVP :=
    { (predV v2c.verb) with adv := compWithPrep }
  { base with c2 := v2c.objPrep }

def fillSlashPreservingBase (vps : EnglishVPSlash) (obj : EnglishNP) : EnglishVP :=
  let objStr :=
    if vps.c2 == "" then obj.s .NPAcc
    else vps.c2 ++ " " ++ obj.s .NPAcc
  let baseComp := vps.toEnglishVP.compl (.AgP3Sg .Neutr)
  let combined :=
    if baseComp == "" then objStr
    else if objStr == "" then baseComp
    else baseComp ++ " " ++ objStr
  { vps.toEnglishVP with compl := fun _ => combined }

def applyCompVerb (v2c : EnglishV2CompFrame) (compText : String) : EnglishVP :=
  let compWithPrep := addCompPrep v2c.compPrep compText
  { (predV v2c.verb) with adv := compWithPrep }

def fixedClause (s : String) : EnglishClause :=
  { s := fun _ _ _ _ => s }

def fixedQClause (s : String) : EnglishClause :=
  { s := fun _ _ _ ord =>
      match ord with
      | .OQuest => s
      | _ => s }

def prefixNP (pfx : String) (np : EnglishNP) : EnglishNP :=
  { s := fun npc => joinWords [pfx, np.s npc]
    agr := np.agr }

def suffixNP (np : EnglishNP) (sfx : String) : EnglishNP :=
  { s := fun npc => joinWords [np.s npc, sfx]
    agr := np.agr }

def unitsWord : Nat → String
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
  | 3 => "three"
  | 4 => "four"
  | 5 => "five"
  | 6 => "six"
  | 7 => "seven"
  | 8 => "eight"
  | _ => "nine"

def teenWord : Nat → String
  | 10 => "ten"
  | 11 => "eleven"
  | 12 => "twelve"
  | 13 => "thirteen"
  | 14 => "fourteen"
  | 15 => "fifteen"
  | 16 => "sixteen"
  | 17 => "seventeen"
  | 18 => "eighteen"
  | _ => "nineteen"

def tensWord : Nat → String
  | 2 => "twenty"
  | 3 => "thirty"
  | 4 => "forty"
  | 5 => "fifty"
  | 6 => "sixty"
  | 7 => "seventy"
  | 8 => "eighty"
  | _ => "ninety"

partial def natCardinalWords : Nat → String
  | n =>
    if n < 10 then
      unitsWord n
    else if n < 20 then
      teenWord n
    else if n < 100 then
      let t := n / 10
      let u := n % 10
      if u = 0 then tensWord t else tensWord t ++ "-" ++ unitsWord u
    else if n < 1000 then
      let h := n / 100
      let r := n % 100
      if r = 0 then unitsWord h ++ " hundred"
      else unitsWord h ++ " hundred " ++ natCardinalWords r
    else if n < 1000000 then
      let th := n / 1000
      let r := n % 1000
      if r = 0 then natCardinalWords th ++ " thousand"
      else natCardinalWords th ++ " thousand " ++ natCardinalWords r
    else if n < 1000000000 then
      let m := n / 1000000
      let r := n % 1000000
      if r = 0 then natCardinalWords m ++ " million"
      else natCardinalWords m ++ " million " ++ natCardinalWords r
    else
      let b := n / 1000000000
      let r := n % 1000000000
      if r = 0 then natCardinalWords b ++ " billion"
      else natCardinalWords b ++ " billion " ++ natCardinalWords r

def stripSuffix? (s suffix : String) : Option String :=
  if strEndsWith s suffix then
    some (strDropEnd s suffix.toList.length)
  else
    none

def ordinalizeCardinal (s : String) : String :=
  match stripSuffix? s "one" with
  | some p => p ++ "first"
  | none =>
    match stripSuffix? s "two" with
    | some p => p ++ "second"
    | none =>
      match stripSuffix? s "three" with
      | some p => p ++ "third"
      | none =>
        match stripSuffix? s "five" with
        | some p => p ++ "fifth"
        | none =>
          match stripSuffix? s "eight" with
          | some p => p ++ "eighth"
          | none =>
            match stripSuffix? s "nine" with
            | some p => p ++ "ninth"
            | none =>
              match stripSuffix? s "twelve" with
              | some p => p ++ "twelfth"
              | none =>
                if strEndsWith s "y" then
                  strDropEnd s 1 ++ "ieth"
                else
                  s ++ "th"

def decimalCardinalWords (s : String) : String :=
  if s.contains '.' then
    let parts := s.splitOn "."
    match parts with
    | [lhs, rhs] =>
      let sign := if lhs.startsWith "-" then "minus " else ""
      let lhsAbs := if lhs.startsWith "-" then lhs.drop 1 else lhs
      let lhsNat? := lhsAbs.toNat?
      let lhsWords := match lhsNat? with | some n => natCardinalWords n | none => lhs
      let rhsWords := String.intercalate " " (rhs.toList.map (fun ch => unitsWord (ch.toNat - '0'.toNat)))
      sign ++ lhsWords ++ " point " ++ rhsWords
    | _ => s
  else
    match s.toNat? with
    | some n => natCardinalWords n
    | none => s

def passiveVP (v2 : EnglishV2) : EnglishVP :=
  { inf := "be"
    pres := fun agr => auxBe.pres .Pos agr
    past := "was"
    ppart := "been"
    prpart := "being"
    particle := ""
    compl := fun _ =>
      if v2.c2 == "" then v2.toEnglishVerb.s .VPPart
      else v2.toEnglishVerb.s .VPPart ++ " " ++ v2.c2
    adv := "" }

def parseNatCard? (s : String) : Option Nat :=
  s.toNat?

def cardNat (n : Nat) : EngValue :=
  .card (toString n)

def mulCard? (a b : String) : Option EngValue := do
  let x ← parseNatCard? a
  let y ← parseNatCard? b
  pure (cardNat (x * y))

def addCard? (a b : String) : Option EngValue := do
  let x ← parseNatCard? a
  let y ← parseNatCard? b
  pure (cardNat (x + y))

end Mettapedia.Languages.GF.English.Linearization
