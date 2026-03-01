/-
# English Linearization: Abstract Syntax to English Concrete Syntax

Bridges GF abstract syntax trees to English concrete syntax via a typed evaluator.

This module now supports:
1. Category-aware lexical leaves (N/A/V/V2/Det/Pron/Prep/Conj/Subj/Adv)
2. Core compositional constructors (UseN, DetCN, AdjCN, UseV, PredVP, UseCl, etc.)
3. Tense/polarity transport through TTAnt/PPos/PNeg and UseCl/UseQCl/UseRCl
4. Coordination list constructors (Base*/Cons* + Conj*) for key categories
5. Coverage diagnostics against `FunctionSig.allFunctions`

Unknown constructors still linearize deterministically via symbolic fallback,
so coverage expansion can proceed incrementally without returning `∅`.
-/

import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.English.Syntax
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.Languages.GF.English.Relatives
import Mettapedia.Languages.GF.English.Properties

namespace Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Core Abstract
open English
open Syntax Pronouns Relatives
open Nouns Verbs Adjectives

/-! ## English Linearization Environment -/

/-- Environment hooks for overriding lexical entries during linearization.
All hooks default to `none`; built-in fallbacks are then used. -/
structure EnglishLinEnv where
  lookupCN : String → Option EnglishNoun := fun _ => none
  lookupN : String → Option EnglishNoun := fun _ => none
  lookupA : String → Option EnglishAdj := fun _ => none
  lookupV : String → Option EnglishVerb := fun _ => none
  lookupV2 : String → Option EnglishV2 := fun _ => none
  lookupDet : String → Option EnglishDet := fun _ => none
  lookupNP : String → Option EnglishNP := fun _ => none
  lookupAdv : String → Option String := fun _ => none
  lookupPrep : String → Option EnglishPrep := fun _ => none
  lookupConj : String → Option EnglishConj := fun _ => none
  lookupSubj : String → Option EnglishSubj := fun _ => none

/-- Linearize a leaf noun in a case/number context.
Kept as a focused helper/theorem target. -/
def linearizeLeaf (env : EnglishLinEnv) (name : String) (c : Case) (n : Number) : String :=
  match env.lookupCN name <|> env.lookupN name with
  | some cn => cn.s n c
  | none => name

/-! ## Normalization Helpers -/

private def decodeGFToken (s : String) : String :=
  String.ofList <| s.toList.map fun ch =>
    if ch = '_' || ch = '7' || ch = '8' then ' ' else ch

private def dropSuffixIf (s suffix : String) : String :=
  if strEndsWith s suffix then
    strDropEnd s suffix.toList.length
  else s

private def stemFrom (name suffix : String) : String :=
  decodeGFToken (dropSuffixIf name suffix)

private def normalizeInterrogativeStem (s : String) : String :=
  match s with
  | "whatSg" => "what"
  | "whatPl" => "what"
  | "whoSg" => "who"
  | "whoPl" => "who"
  | other => other

private def agrFromNumber (n : Number) : Agr :=
  match n with
  | .Sg => .AgP3Sg .Neutr
  | .Pl => .AgP3Pl

private def mkLiteralNP (txt : String) : EnglishNP :=
  { s := fun _ => txt, agr := .AgP3Sg .Neutr }

private def joinWithConj (xs : List String) (conj : String) : String :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: rest =>
    let rec loop : List String → String
      | [] => ""
      | [y] => y
      | y :: ys => y ++ ", " ++ loop ys
    x ++ " " ++ conj ++ " " ++ loop rest

/-! ## Typed Evaluator Domain -/

structure EnglishTemp where
  tense : Tense := .Pres
  ant : Anteriority := .Simul
  deriving DecidableEq, Repr, Inhabited

structure EnglishQuant where
  sSg : String
  sPl : String
  isDef : Bool := false
  deriving DecidableEq, Repr, Inhabited

structure EnglishNumInfo where
  n : Number := .Sg
  card : String := ""
  deriving DecidableEq, Repr, Inhabited

structure EnglishOrdInfo where
  s : String
  deriving DecidableEq, Repr, Inhabited

structure EnglishComp where
  render : Agr → String

structure EnglishV3Frame where
  verb : EnglishVerb
  c2 : String := ""
  c3 : String := ""

inductive EnglishV2CompKind where
  | vp
  | s
  | qs
  | ap
  deriving DecidableEq, Repr, Inhabited

structure EnglishV2CompFrame where
  verb : EnglishVerb
  objPrep : String := ""
  compPrep : String := ""
  kind : EnglishV2CompKind

structure EnglishQVP where
  s : String

inductive EngValue where
  | noun (n : EnglishNoun)
  | cn (cn : EnglishCN)
  | adj (a : EnglishAdj)
  | ap (ap : EnglishAP)
  | quant (q : EnglishQuant)
  | num (n : EnglishNumInfo)
  | card (s : String)
  | ord (o : EnglishOrdInfo)
  | det (d : EnglishDet)
  | np (np : EnglishNP)
  | verb (v : EnglishVerb)
  | verb2 (v : EnglishV2)
  | verb3 (v : EnglishV3Frame)
  | verb2comp (v : EnglishV2CompFrame)
  | vp (vp : EnglishVP)
  | comp (c : EnglishComp)
  | vpslash (vps : EnglishVPSlash)
  | clslash (cls : EnglishClSlash)
  | qvp (qvp : EnglishQVP)
  | cls (cl : EnglishClause)
  | qcl (cl : EnglishClause)
  | rcl (rcl : EnglishRCl)
  | rs (rs : EnglishRS)
  | rp (rp : EnglishRP)
  | prep (p : EnglishPrep)
  | conj (c : EnglishConj)
  | subj (s : EnglishSubj)
  | adv (s : String)
  | tense (t : Tense)
  | ant (a : Anteriority)
  | temp (t : EnglishTemp)
  | pol (p : CPolarity)
  | listNP (xs : List EnglishNP)
  | listCN (xs : List EnglishCN)
  | listAP (xs : List EnglishAP)
  | listRS (xs : List EnglishRS)
  | listAdv (xs : List String)
  | listAdV (xs : List String)
  | listIAdv (xs : List String)
  | listDet (xs : List EnglishDet)
  | listVPS (xs : List String)
  | listVPI (xs : List String)
  | listVPS2 (xs : List String)
  | listVPI2 (xs : List String)
  | listComp (xs : List String)
  | listImp (xs : List String)
  | listSymb (xs : List String)
  | listS (xs : List String)
  | raw (cat : Category) (txt : String)
  deriving Inhabited

private def EngValue.asN? : EngValue → Option EnglishNoun
  | EngValue.noun x => some x
  | EngValue.cn x => some x
  | _ => none

private def EngValue.asCN? : EngValue → Option EnglishCN
  | EngValue.cn x => some x
  | EngValue.noun x => some x
  | _ => none

private def EngValue.asA? : EngValue → Option EnglishAdj
  | EngValue.adj x => some x
  | _ => none

private def EngValue.asAP? : EngValue → Option EnglishAP
  | EngValue.ap x => some x
  | _ => none

private def EngValue.asDet? : EngValue → Option EnglishDet
  | EngValue.det x => some x
  | _ => none

private def EngValue.asQuant? : EngValue → Option EnglishQuant
  | EngValue.quant q => some q
  | EngValue.det d => some { sSg := d.s, sPl := d.s, isDef := d.isDef }
  | _ => none

private def EngValue.asNum? : EngValue → Option EnglishNumInfo
  | EngValue.num n => some n
  | _ => none

private def EngValue.asCard? : EngValue → Option String
  | EngValue.card s => some s
  | EngValue.raw (.base "Card") s => some s
  | _ => none

private def EngValue.asOrd? : EngValue → Option EnglishOrdInfo
  | EngValue.ord o => some o
  | _ => none

private def EngValue.asNP? : EngValue → Option EnglishNP
  | EngValue.np x => some x
  | _ => none

private def EngValue.asV? : EngValue → Option EnglishVerb
  | EngValue.verb x => some x
  | _ => none

private def EngValue.asV2? : EngValue → Option EnglishV2
  | EngValue.verb2 x => some x
  | _ => none

private def EngValue.asV3? : EngValue → Option EnglishV3Frame
  | EngValue.verb3 x => some x
  | _ => none

private def EngValue.asV2Comp? : EngValue → Option EnglishV2CompFrame
  | EngValue.verb2comp x => some x
  | _ => none

private def EngValue.asVP? : EngValue → Option EnglishVP
  | EngValue.vp x => some x
  | _ => none

private def EngValue.asComp? : EngValue → Option EnglishComp
  | EngValue.comp x => some x
  | _ => none

private def EngValue.asVPSlash? : EngValue → Option EnglishVPSlash
  | EngValue.vpslash x => some x
  | _ => none

private def EngValue.asClSlash? : EngValue → Option EnglishClSlash
  | EngValue.clslash x => some x
  | _ => none

private def EngValue.asQVP? : EngValue → Option EnglishQVP
  | EngValue.qvp x => some x
  | EngValue.raw (.base "QVP") s => some ⟨s⟩
  | _ => none

private def EngValue.asCl? : EngValue → Option EnglishClause
  | EngValue.cls x => some x
  | _ => none

private def EngValue.asQCl? : EngValue → Option EnglishClause
  | EngValue.qcl x => some x
  | _ => none

private def EngValue.asRCl? : EngValue → Option EnglishRCl
  | EngValue.rcl x => some x
  | _ => none

private def EngValue.asRS? : EngValue → Option EnglishRS
  | EngValue.rs x => some x
  | _ => none

private def EngValue.asRP? : EngValue → Option EnglishRP
  | EngValue.rp x => some x
  | _ => none

private def EngValue.asPrep? : EngValue → Option EnglishPrep
  | EngValue.prep x => some x
  | _ => none

private def EngValue.asConj? : EngValue → Option EnglishConj
  | EngValue.conj x => some x
  | _ => none

private def EngValue.asSubj? : EngValue → Option EnglishSubj
  | EngValue.subj x => some x
  | _ => none

private def EngValue.asAdv? : EngValue → Option String
  | EngValue.adv x => some x
  | EngValue.raw (.base "Adv") x => some x
  | EngValue.raw (.base "AdV") x => some x
  | EngValue.raw (.base "IAdv") x => some x
  | _ => none

private def EngValue.asPConj? : EngValue → Option String
  | EngValue.raw (.base "PConj") x => some x
  | _ => none

private def EngValue.asVoc? : EngValue → Option String
  | EngValue.raw (.base "Voc") x => some x
  | _ => none

private def EngValue.asTemp? : EngValue → Option EnglishTemp
  | EngValue.temp x => some x
  | EngValue.tense x => some ⟨x, .Simul⟩
  | _ => none

private def EngValue.asPol? : EngValue → Option CPolarity
  | EngValue.pol x => some x
  | _ => none

private def EngValue.asListNP? : EngValue → Option (List EnglishNP)
  | EngValue.listNP xs => some xs
  | EngValue.np x => some [x]
  | _ => none

private def EngValue.asListCN? : EngValue → Option (List EnglishCN)
  | EngValue.listCN xs => some xs
  | EngValue.cn x => some [x]
  | EngValue.noun x => some [x]
  | _ => none

private def EngValue.asListAP? : EngValue → Option (List EnglishAP)
  | EngValue.listAP xs => some xs
  | EngValue.ap x => some [x]
  | _ => none

private def EngValue.asListRS? : EngValue → Option (List EnglishRS)
  | EngValue.listRS xs => some xs
  | EngValue.rs x => some [x]
  | _ => none

private def EngValue.asListAdv? : EngValue → Option (List String)
  | EngValue.listAdv xs => some xs
  | EngValue.adv x => some [x]
  | EngValue.raw (.base "Adv") x => some [x]
  | _ => none

private def EngValue.asListAdV? : EngValue → Option (List String)
  | EngValue.listAdV xs => some xs
  | EngValue.adv x => some [x]
  | EngValue.raw (.base "AdV") x => some [x]
  | _ => none

private def EngValue.asListIAdv? : EngValue → Option (List String)
  | EngValue.listIAdv xs => some xs
  | EngValue.adv x => some [x]
  | EngValue.raw (.base "IAdv") x => some [x]
  | _ => none

private def EngValue.asListDet? : EngValue → Option (List EnglishDet)
  | EngValue.listDet xs => some xs
  | EngValue.det d => some [d]
  | _ => none

private def EngValue.asListS? : EngValue → Option (List String)
  | EngValue.listS xs => some xs
  | EngValue.raw (.base "S") s => some [s]
  | EngValue.raw (.base "QS") s => some [s]
  | EngValue.raw (.base "SC") s => some [s]
  | _ => none

private def EngValue.asListVPS? : EngValue → Option (List String)
  | EngValue.listVPS xs => some xs
  | EngValue.raw (.base "VPS") s => some [s]
  | _ => none

private def EngValue.asListVPI? : EngValue → Option (List String)
  | EngValue.listVPI xs => some xs
  | EngValue.raw (.base "VPI") s => some [s]
  | _ => none

private def EngValue.asListVPS2? : EngValue → Option (List String)
  | EngValue.listVPS2 xs => some xs
  | EngValue.raw (.base "VPS2") s => some [s]
  | _ => none

private def EngValue.asListVPI2? : EngValue → Option (List String)
  | EngValue.listVPI2 xs => some xs
  | EngValue.raw (.base "VPI2") s => some [s]
  | _ => none

private def EngValue.asListComp? : EngValue → Option (List String)
  | EngValue.listComp xs => some xs
  | EngValue.comp c => some [c.render (.AgP3Sg .Neutr)]
  | EngValue.raw (.base "Comp") s => some [s]
  | _ => none

private def EngValue.asListImp? : EngValue → Option (List String)
  | EngValue.listImp xs => some xs
  | EngValue.raw (.base "Imp") s => some [s]
  | _ => none

private def EngValue.asListSymb? : EngValue → Option (List String)
  | EngValue.listSymb xs => some xs
  | EngValue.raw (.base "Symb") s => some [s]
  | _ => none

private def copulaVP (renderComp : Agr → String) : EnglishVP :=
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

private def addCompPrep (prep : String) (s : String) : String :=
  if prep == "" then s else prep ++ " " ++ s

private def vpCompSurface (vp : EnglishVP) : String :=
  joinWords [vp.inf, vp.particle, vp.compl (.AgP3Sg .Neutr), vp.adv]

private def applyV3Slash (v3 : EnglishV3Frame) (filled : String) (missingPrep : String) : EnglishVPSlash :=
  let base : EnglishVP :=
    { (predV v3.verb) with compl := fun _ => filled }
  { base with c2 := missingPrep }

private def applyV2CompSlash (v2c : EnglishV2CompFrame) (compText : String) : EnglishVPSlash :=
  let compWithPrep := addCompPrep v2c.compPrep compText
  let base : EnglishVP :=
    { (predV v2c.verb) with adv := compWithPrep }
  { base with c2 := v2c.objPrep }

private def fillSlashPreservingBase (vps : EnglishVPSlash) (obj : EnglishNP) : EnglishVP :=
  let objStr :=
    if vps.c2 == "" then obj.s .NPAcc
    else vps.c2 ++ " " ++ obj.s .NPAcc
  let baseComp := vps.toEnglishVP.compl (.AgP3Sg .Neutr)
  let combined :=
    if baseComp == "" then objStr
    else if objStr == "" then baseComp
    else baseComp ++ " " ++ objStr
  { vps.toEnglishVP with compl := fun _ => combined }

private def applyCompVerb (v2c : EnglishV2CompFrame) (compText : String) : EnglishVP :=
  let compWithPrep := addCompPrep v2c.compPrep compText
  { (predV v2c.verb) with adv := compWithPrep }

private def fixedClause (s : String) : EnglishClause :=
  { s := fun _ _ _ _ => s }

private def fixedQClause (s : String) : EnglishClause :=
  { s := fun _ _ _ ord =>
      match ord with
      | .OQuest => s
      | _ => s }

private def prefixNP (pfx : String) (np : EnglishNP) : EnglishNP :=
  { s := fun npc => joinWords [pfx, np.s npc]
    agr := np.agr }

private def suffixNP (np : EnglishNP) (sfx : String) : EnglishNP :=
  { s := fun npc => joinWords [np.s npc, sfx]
    agr := np.agr }

private def unitsWord : Nat → String
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

private def teenWord : Nat → String
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

private def tensWord : Nat → String
  | 2 => "twenty"
  | 3 => "thirty"
  | 4 => "forty"
  | 5 => "fifty"
  | 6 => "sixty"
  | 7 => "seventy"
  | 8 => "eighty"
  | _ => "ninety"

private partial def natCardinalWords : Nat → String
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

private def stripSuffix? (s suffix : String) : Option String :=
  if strEndsWith s suffix then
    some (strDropEnd s suffix.toList.length)
  else
    none

private def ordinalizeCardinal (s : String) : String :=
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

private def decimalCardinalWords (s : String) : String :=
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

private def passiveVP (v2 : EnglishV2) : EnglishVP :=
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

private def parseNatCard? (s : String) : Option Nat :=
  s.toNat?

private def cardNat (n : Nat) : EngValue :=
  .card (toString n)

private def mulCard? (a b : String) : Option EngValue := do
  let x ← parseNatCard? a
  let y ← parseNatCard? b
  pure (cardNat (x * y))

private def addCard? (a b : String) : Option EngValue := do
  let x ← parseNatCard? a
  let y ← parseNatCard? b
  pure (cardNat (x + y))

structure RenderParams where
  case : Case := .Nom
  number : Number := .Sg
  tense : Tense := .Pres
  ant : Anteriority := .Simul
  pol : CPolarity := .CPos
  order : Order := .ODir true
  deriving DecidableEq, Repr, Inhabited

private def renderValue (v : EngValue) (p : RenderParams) : String :=
  match v with
  | .noun n => n.s p.number p.case
  | .cn cn => cn.s p.number p.case
  | .adj a => a.s (.AAdj .Pos p.case)
  | .ap ap => ap.s (agrFromNumber p.number)
  | .quant q => if p.number == .Pl then q.sPl else q.sSg
  | .num n => if n.card == "" then (if n.n == .Pl then "plural" else "singular") else n.card
  | .card s => s
  | .ord o => o.s
  | .det d => d.s
  | .np np => np.s (.NCase p.case)
  | .verb v => v.s .VInf
  | .verb2 v2 => v2.toEnglishVerb.s .VInf
  | .verb3 v3 => v3.verb.s .VInf
  | .verb2comp v2c => v2c.verb.s .VInf
  | .vp vp =>
    let cl := mkClause "it" (.AgP3Sg .Neutr) vp
    cl.s p.tense p.ant p.pol p.order
  | .comp c =>
    c.render (agrFromNumber p.number)
  | .vpslash vps =>
    let cl := mkClause "it" (.AgP3Sg .Neutr) vps.toEnglishVP
    cl.s p.tense p.ant p.pol p.order
  | .clslash cls =>
    cls.s p.tense p.ant p.pol p.order
  | .qvp qvp =>
    qvp.s
  | .cls cl => cl.s p.tense p.ant p.pol p.order
  | .qcl cl => cl.s p.tense p.ant p.pol .OQuest
  | .rcl rcl => rcl.s p.tense p.ant p.pol (agrFromNumber p.number)
  | .rs rs => rs.s (agrFromNumber p.number)
  | .rp rp => rp.s (.RC .Neutr (.NCase .Nom))
  | .prep prep => prep.s
  | .conj conj => conj.s2
  | .subj subj => subj.s
  | .adv s => s
  | .tense .Pres => "present"
  | .tense .Past => "past"
  | .tense .Fut => "future"
  | .tense .Cond => "conditional"
  | .ant .Simul => "simple"
  | .ant .Anter => "perfect"
  | .temp t =>
    let tstr := match t.tense with
      | .Pres => "present"
      | .Past => "past"
      | .Fut => "future"
      | .Cond => "conditional"
    let astr := match t.ant with
      | .Simul => "simple"
      | .Anter => "perfect"
    tstr ++ " " ++ astr
  | .pol .CPos => "positive"
  | .pol (.CNeg true) => "negative contracted"
  | .pol (.CNeg false) => "negative"
  | .listNP xs => joinWithConj (xs.map (fun np => np.s (.NCase p.case))) "and"
  | .listCN xs => joinWithConj (xs.map (fun cn => cn.s p.number p.case)) "and"
  | .listAP xs => joinWithConj (xs.map (fun ap => ap.s (agrFromNumber p.number))) "and"
  | .listRS xs => joinWithConj (xs.map (fun rs => rs.s (.AgP3Sg .Neutr))) "and"
  | .listAdv xs => joinWithConj xs "and"
  | .listAdV xs => joinWithConj xs "and"
  | .listIAdv xs => joinWithConj xs "and"
  | .listDet xs => joinWithConj (xs.map (fun d => d.s)) "and"
  | .listVPS xs => joinWithConj xs "and"
  | .listVPI xs => joinWithConj xs "and"
  | .listVPS2 xs => joinWithConj xs "and"
  | .listVPI2 xs => joinWithConj xs "and"
  | .listComp xs => joinWithConj xs "and"
  | .listImp xs => joinWithConj xs "and"
  | .listSymb xs => joinWithConj xs "and"
  | .listS xs => joinWithConj xs "and"
  | .raw _ txt => txt

private def fallbackAppString (name : String) (args : List EngValue) : String :=
  let rendered := args.map (fun v => renderValue v {})
  name ++ "(" ++ String.intercalate ", " rendered ++ ")"

/-! ## Lexical Leaves -/

private def nounByName? (name : String) : Option EnglishNoun :=
  match name with
  | "man_N" => some man_N
  | "woman_N" => some woman_N
  | "child_N" => some child_N
  | "foot_N" => some foot_N
  | "tooth_N" => some tooth_N
  | "mouse_N" => some mouse_N
  | "person_N" => some person_N
  | "ox_N" => some ox_N
  | _ => none

private def adjByName? (name : String) : Option EnglishAdj :=
  match name with
  | "good_A" => some good_A
  | "bad_A" => some bad_A
  | "far_A" => some far_A
  | "beautiful_A" => some beautiful_A
  | "important_A" => some important_A
  | "interesting_A" => some interesting_A
  | _ => none

private def verbByName? (name : String) : Option EnglishVerb :=
  match name with
  | "be_V" => some be_V
  | "have_V" => some have_V
  | "do_V" => some do_V
  | "go_V" => some go_V
  | "eat_V" => some eat_V
  | "drink_V" => some drink_V
  | "sing_V" => some sing_V
  | "run_V" => some run_V
  | "swim_V" => some swim_V
  | "give_V" => some give_V
  | "take_V" => some take_V
  | "sleep_V" => some sleep_V
  | "say_V" => some say_V
  | "hear_V" => some hear_V
  | "write_V" => some write_V
  | "read_V" => some read_V
  | _ => none

private def v2ByName? (name : String) : Option EnglishV2 :=
  match name with
  | "love_V2" => some love_V2
  | "see_V2" => some see_V2
  | "eat_V2" => some eat_V2
  | "give_V2" => some give_V2
  | "take_V2" => some take_V2
  | "drink_V2" => some drink_V2
  | "kill_V2" => some kill_V2
  | "read_V2" => some read_V2
  | "lookAt_V2" => some lookAt_V2
  | "waitFor_V2" => some waitFor_V2
  | "listenTo_V2" => some listenTo_V2
  | "write_V2" => some write_V2
  | "say_V2" => some say_V2
  | "hear_V2" => some hear_V2
  | "have_V2" => some (mkV2 have_V)
  | _ => none

private def pronByName? (name : String) : Option EnglishNP :=
  match name with
  | "i_Pron" => some i_Pron
  | "we_Pron" => some we_Pron
  | "youSg_Pron" => some youSg_Pron
  | "youPl_Pron" => some youPl_Pron
  | "youPol_Pron" => some youPl_Pron
  | "he_Pron" => some he_Pron
  | "she_Pron" => some she_Pron
  | "it_Pron" => some it_Pron
  | "they_Pron" => some they_Pron
  | _ => none

private def detByName? (name : String) : Option EnglishDet :=
  match name with
  | "every_Det" => some every_Det
  | "few_Det" => some few_Det
  | "many_Det" => some many_Det
  | "someSg_Det" => some some_Det
  | "somePl_Det" => some { some_Det with n := .Pl }
  | "the_Det" => some theDefArt
  | "a_Det" => some aIndefArt
  | "this_Det" => some this_Det
  | "that_Det" => some that_Det
  | "these_Det" => some these_Det
  | "those_Det" => some those_Det
  | _ => none

private def prepByName? (name : String) : Option EnglishPrep :=
  match name with
  | "in_Prep" => some in_Prep
  | "on_Prep" => some on_Prep
  | "to_Prep" => some to_Prep
  | "from_Prep" => some from_Prep
  | "with_Prep" => some with_Prep
  | "by_Prep" | "by8agent_Prep" | "by8means_Prep" => some by_Prep
  | "for_Prep" => some for_Prep
  | "of_Prep" | "possess_Prep" => some of_Prep
  | "at_Prep" => some at_Prep
  | _ => none

private def conjByName? (name : String) : Option EnglishConj :=
  match name with
  | "and_Conj" => some and_Conj
  | "or_Conj" => some or_Conj
  | "both7and_DConj" => some both_and_Conj
  | "either7or_DConj" => some either_or_Conj
  | "neither7nor_DConj" => some neither_nor_Conj
  | _ => none

private def subjByName? (name : String) : Option EnglishSubj :=
  match name with
  | "when_Subj" => some when_Subj
  | "if_Subj" => some if_Subj
  | "because_Subj" => some because_Subj
  | "although_Subj" => some although_Subj
  | "that_Subj" => some that_Subj
  | "before_Subj" => some before_Subj
  | "after_Subj" => some after_Subj
  | "while_Subj" => some while_Subj
  | _ => none

private def quantByName? (name : String) : Option EnglishQuant :=
  match name with
  | "no_Quant" => some { sSg := "no", sPl := "no", isDef := false }
  | "this_Quant" => some { sSg := "this", sPl := "these", isDef := true }
  | "that_Quant" => some { sSg := "that", sPl := "those", isDef := true }
  | _ => none

private def v3ByName? (name : String) : Option EnglishV3Frame :=
  match name with
  | "add_V3" => some { verb := regV "add", c2 := "", c3 := "to" }
  | "give_V3" => some { verb := give_V, c2 := "", c3 := "to" }
  | "sell_V3" => some { verb := regV "sell", c2 := "", c3 := "to" }
  | "send_V3" => some { verb := regV "send", c2 := "", c3 := "to" }
  | "talk_V3" => some { verb := regV "talk", c2 := "to", c3 := "about" }
  | _ => none

private def v2compByName? (name : String) : Option EnglishV2CompFrame :=
  match name with
  | "can8know_VV" => some { verb := mk5V "can" "can" "could" "could" "can", objPrep := "", compPrep := "", kind := .vp }
  | "can_VV" => some { verb := mk5V "can" "can" "could" "could" "can", objPrep := "", compPrep := "", kind := .vp }
  | "must_VV" => some { verb := mk5V "must" "must" "must" "must" "must", objPrep := "", compPrep := "", kind := .vp }
  | "want_VV" => some { verb := regV "want", objPrep := "", compPrep := "to", kind := .vp }
  | "fear_VS" => some { verb := regV "fear", objPrep := "", compPrep := "that", kind := .s }
  | "hope_VS" => some { verb := regV "hope", objPrep := "", compPrep := "that", kind := .s }
  | "know_VS" => some { verb := regV "know", objPrep := "", compPrep := "that", kind := .s }
  | "say_VS" => some { verb := regV "say", objPrep := "", compPrep := "that", kind := .s }
  | "know_VQ" => some { verb := regV "know", objPrep := "", compPrep := "", kind := .qs }
  | "wonder_VQ" => some { verb := regV "wonder", objPrep := "", compPrep := "", kind := .qs }
  | "become_VA" => some { verb := regV "become", objPrep := "", compPrep := "", kind := .ap }
  | "beg_V2V" => some { verb := regV "beg", objPrep := "", compPrep := "to", kind := .vp }
  | "answer_V2S" => some { verb := regV "answer", objPrep := "", compPrep := "that", kind := .s }
  | "ask_V2Q" => some { verb := regV "ask", objPrep := "", compPrep := "", kind := .qs }
  | "paint_V2A" => some { verb := regV "paint", objPrep := "", compPrep := "", kind := .ap }
  | _ => none

private def digitByName? (name : String) : Option String :=
  match name with
  | "n2" | "D_2" => some "2"
  | "n3" | "D_3" => some "3"
  | "n4" | "D_4" => some "4"
  | "n5" | "D_5" => some "5"
  | "n6" | "D_6" => some "6"
  | "n7" | "D_7" => some "7"
  | "n8" | "D_8" => some "8"
  | "n9" | "D_9" => some "9"
  | "D_0" => some "0"
  | "D_1" => some "1"
  | _ => none

private def evalLeafValue (env : EnglishLinEnv) (name : String) (cat : Category) : EngValue :=
  match cat with
  | .base "N" =>
    match env.lookupN name <|> env.lookupCN name <|> nounByName? name with
    | some n => .noun n
    | none => .noun (regN (stemFrom name "_N"))
  | .base "CN" =>
    match env.lookupCN name <|> env.lookupN name <|> nounByName? name with
    | some cn => .cn cn
    | none =>
      let stem :=
        if strEndsWith name "_N" then stemFrom name "_N" else stemFrom name "_CN"
      .cn (regN stem)
  | .base "N2" =>
    .raw cat (stemFrom name "_N2")
  | .base "N3" =>
    .raw cat (stemFrom name "_N3")
  | .base "A" =>
    match env.lookupA name <|> adjByName? name with
    | some a => .adj a
    | none => .adj (compoundA (stemFrom name "_A"))
  | .base "A2" =>
    .raw cat (stemFrom name "_A2")
  | .base "Predet" =>
    .raw cat (stemFrom name "_Predet")
  | .base "AdA" =>
    .raw cat (stemFrom name "_AdA")
  | .base "AdN" =>
    .raw cat (stemFrom name "_AdN")
  | .base "CAdv" =>
    .raw cat (stemFrom name "_CAdv")
  | .base "V" =>
    match env.lookupV name <|> verbByName? name with
    | some v => .verb v
    | none => .verb (regV (stemFrom name "_V"))
  | .base "V2" =>
    match env.lookupV2 name <|> v2ByName? name with
    | some v2 => .verb2 v2
    | none => .verb2 (regV2 (stemFrom name "_V2"))
  | .base "VV" =>
    match v2compByName? name with
    | some vv => .verb2comp vv
    | none => .verb2comp { verb := regV (stemFrom name "_VV"), objPrep := "", compPrep := "", kind := .vp }
  | .base "VS" =>
    match v2compByName? name with
    | some vs => .verb2comp vs
    | none => .verb2comp { verb := regV (stemFrom name "_VS"), objPrep := "", compPrep := "that", kind := .s }
  | .base "VQ" =>
    match v2compByName? name with
    | some vq => .verb2comp vq
    | none => .verb2comp { verb := regV (stemFrom name "_VQ"), objPrep := "", compPrep := "", kind := .qs }
  | .base "VA" =>
    match v2compByName? name with
    | some va => .verb2comp va
    | none => .verb2comp { verb := regV (stemFrom name "_VA"), objPrep := "", compPrep := "", kind := .ap }
  | .base "V3" =>
    match v3ByName? name with
    | some v3 => .verb3 v3
    | none => .verb3 { verb := regV (stemFrom name "_V3"), c2 := "", c3 := "" }
  | .base "V2V" =>
    match v2compByName? name with
    | some v2c => .verb2comp v2c
    | none => .verb2comp { verb := regV (stemFrom name "_V2V"), objPrep := "", compPrep := "to", kind := .vp }
  | .base "V2S" =>
    match v2compByName? name with
    | some v2c => .verb2comp v2c
    | none => .verb2comp { verb := regV (stemFrom name "_V2S"), objPrep := "", compPrep := "that", kind := .s }
  | .base "V2Q" =>
    match v2compByName? name with
    | some v2c => .verb2comp v2c
    | none => .verb2comp { verb := regV (stemFrom name "_V2Q"), objPrep := "", compPrep := "", kind := .qs }
  | .base "V2A" =>
    match v2compByName? name with
    | some v2c => .verb2comp v2c
    | none => .verb2comp { verb := regV (stemFrom name "_V2A"), objPrep := "", compPrep := "", kind := .ap }
  | .base "Quant" =>
    match quantByName? name with
    | some q => .quant q
    | none =>
      if name = "DefArt" then .quant { sSg := "the", sPl := "the", isDef := true }
      else if name = "IndefArt" then .quant { sSg := "a", sPl := "some", isDef := false }
      else .quant { sSg := decodeGFToken name, sPl := decodeGFToken name, isDef := false }
  | .base "Num" =>
    if name = "NumPl" then .num { n := .Pl, card := "" }
    else .num { n := .Sg, card := "" }
  | .base "Card" =>
    .card (stemFrom name "_Card")
  | .base "Ord" =>
    .ord { s := stemFrom name "_Ord" }
  | .base "Digit" =>
    match digitByName? name with
    | some d => .card d
    | none => .card (decodeGFToken name)
  | .base "Dig" =>
    match digitByName? name with
    | some d => .card d
    | none => .card (decodeGFToken name)
  | .base "Digits" =>
    .card (decodeGFToken name)
  | .base "Decimal" =>
    .card (decodeGFToken name)
  | .base "Numeral" =>
    .card (decodeGFToken name)
  | .base "Sub10" =>
    if name = "pot01" then .card "1" else .card (decodeGFToken name)
  | .base "Sub100" =>
    if name = "pot110" then .card "10"
    else if name = "pot111" then .card "11"
    else .card (decodeGFToken name)
  | .base "Sub1000" =>
    if name = "pot21" then .card "100" else .card (decodeGFToken name)
  | .base "Sub1000000" =>
    if name = "pot31" then .card "1000000" else .card (decodeGFToken name)
  | .base "Sub1000000000" =>
    if name = "pot41" then .card "1000000000" else .card (decodeGFToken name)
  | .base "Sub1000000000000" =>
    if name = "pot51" then .card "1000000000000" else .card (decodeGFToken name)
  | .base "Det" =>
    match env.lookupDet name <|> detByName? name with
    | some d => .det d
    | none => .det { s := stemFrom name "_Det", n := .Sg, isDef := false }
  | .base "Pron" =>
    match pronByName? name with
    | some p => .np p
    | none => .np (mkLiteralNP (stemFrom name "_Pron"))
  | .base "NP" =>
    match env.lookupNP name with
    | some np => .np np
    | none => .np (mkLiteralNP (decodeGFToken name))
  | .base "Adv" =>
    match env.lookupAdv name with
    | some a => .adv a
    | none => .adv (stemFrom name "_Adv")
  | .base "AdV" =>
    .adv (stemFrom name "_AdV")
  | .base "IAdv" =>
    .adv (normalizeInterrogativeStem (stemFrom name "_IAdv"))
  | .base "IP" =>
    .raw cat (normalizeInterrogativeStem (stemFrom name "_IP"))
  | .base "IComp" =>
    .raw cat (normalizeInterrogativeStem (stemFrom name "_IComp"))
  | .base "IDet" =>
    .raw cat (normalizeInterrogativeStem (stemFrom name "_IDet"))
  | .base "IQuant" =>
    .raw cat (normalizeInterrogativeStem (stemFrom name "_IQuant"))
  | .base "DAP" =>
    .det { s := stemFrom name "_DAP", n := .Sg, isDef := false }
  | .base "Interj" =>
    .raw cat (stemFrom name "_Interj")
  | .base "Text" =>
    .raw cat (stemFrom name "_Text")
  | .base "PConj" =>
    .raw cat (stemFrom name "_PConj")
  | .base "Voc" =>
    .raw cat (stemFrom name "_Voc")
  | .base "RP" =>
    .raw cat (stemFrom name "_RP")
  | .base "Prep" =>
    match env.lookupPrep name <|> prepByName? name with
    | some p => .prep p
    | none => .prep (mkPrep (stemFrom name "_Prep"))
  | .base "Conj" =>
    match env.lookupConj name <|> conjByName? name with
    | some c => .conj c
    | none => .conj { s1 := "", s2 := stemFrom name "_Conj", n := .Pl }
  | .base "Subj" =>
    match env.lookupSubj name <|> subjByName? name with
    | some s => .subj s
    | none => .subj { s := stemFrom name "_Subj" }
  | .base "Tense" =>
    match name with
    | "TPres" => .tense .Pres
    | "TPast" | "TPastSimple" => .tense .Past
    | "TFut" => .tense .Fut
    | "TCond" => .tense .Cond
    | _ => .tense .Pres
  | .base "Ant" =>
    match name with
    | "ASimul" => .ant .Simul
    | "AAnter" => .ant .Anter
    | _ => .ant .Simul
  | .base "Pol" =>
    match name with
    | "PPos" => .pol .CPos
    | "PNeg" => .pol (.CNeg false)
    | _ => .pol .CPos
  | _ => .raw cat (decodeGFToken name)

/-! ## Core Apply Dispatch -/

private def dispatchApply (f : FunctionSig) (args : List EngValue) : Option EngValue :=
  match f.name, args with
  -- Core noun phrase pipeline
  | "UseN", [x] => x.asN? |>.map (fun n => .cn (linUseN n))
  | "AdNum", [adn, card] =>
    some (.card (joinWords [renderValue adn {}, renderValue card {}]))
  | "OrdNumeralSuperl", [num, a] =>
    match a.asA? with
    | some adj =>
      let base := decimalCardinalWords (renderValue num {})
      let ord := ordinalizeCardinal base
      some (.ord { s := joinWords ["most", adj.s (.AAdj .Pos .Nom), ord] })
    | none => none
  | "ComplN2", [n2, np] =>
    match np.asNP? with
    | some n => some (.cn (regN (joinWords [renderValue n2 {}, "of", n.s (.NCase .Nom)])))
    | none => none
  | "ComplN3", [n3, np] =>
    match np.asNP? with
    | some n => some (.raw Category.N2 (joinWords [renderValue n3 {}, n.s (.NCase .Nom)]))
    | none => none
  | "UseN2", [n2] =>
    some (.cn (regN (renderValue n2 {})))
  | "Use2N3", [n3] =>
    some (.raw Category.N2 (joinWords [renderValue n3 {}, "of"]))
  | "Use3N3", [n3] =>
    some (.raw Category.N2 (joinWords [renderValue n3 {}, "to"]))
  | "SentCN", [cn, sc] =>
    match cn.asCN?, sc.asListS? with
    | some n, some [s] => some (.cn (regN (joinWords [n.s .Sg .Nom, "that", s])))
    | _, _ => none
  | "ApposCN", [cn, np] =>
    match cn.asCN?, np.asNP? with
    | some n, some x => some (.cn (regN (joinWords [n.s .Sg .Nom, x.s (.NCase .Nom)])))
    | _, _ => none
  | "PossNP", [cn, np] =>
    match cn.asCN?, np.asNP? with
    | some n, some x => some (.cn (regN (joinWords [x.s (.NCase .Gen), n.s .Sg .Nom])))
    | _, _ => none
  | "PartNP", [cn, np] =>
    match cn.asCN?, np.asNP? with
    | some n, some x => some (.cn (regN (joinWords [n.s .Sg .Nom, "of", x.s (.NCase .Nom)])))
    | _, _ => none
  | "AdjDAP", [dap, ap] =>
    match dap.asDet?, ap.asAP? with
    | some d, some a => some (.det { d with s := joinWords [a.s (agrFromNumber d.n), d.s] })
    | _, _ => none
  | "DetDAP", [d] => d.asDet? |>.map .det
  | "ComplA2", [a2, np] =>
    match np.asNP? with
    | some n =>
      some (.ap
        { s := fun _ => joinWords [renderValue a2 {}, n.s .NPAcc]
          isPre := false })
    | none => none
  | "ReflA2", [a2] =>
    some (.ap
      { s := fun _ => joinWords [renderValue a2 {}, "itself"]
        isPre := false })
  | "UseA2", [a2] =>
    some (.ap
      { s := fun _ => renderValue a2 {}
        isPre := true })
  | "UseComparA", [a] =>
    match a.asA? with
    | some adj => some (.ap { s := fun _ => adj.s (.AAdj .Comp .Nom), isPre := true })
    | none => none
  | "CAdvAP", [cadv, ap, np] =>
    match ap.asAP?, np.asNP? with
    | some a, some n =>
      some (.ap
        { s := fun agr => joinWords [renderValue cadv {}, a.s agr, n.s .NPAcc]
          isPre := false })
    | _, _ => none
  | "AdjOrd", [ord] =>
    match ord.asOrd? with
    | some o => some (.ap { s := fun _ => o.s, isPre := true })
    | none => none
  | "SentAP", [ap, sc] =>
    match ap.asAP?, sc.asListS? with
    | some a, some [s] =>
      some (.ap
        { s := fun agr => joinWords [a.s agr, "that", s]
          isPre := false })
    | _, _ => none
  | "AdAP", [ada, ap] =>
    match ap.asAP? with
    | some a =>
      some (.ap
        { s := fun agr => joinWords [renderValue ada {}, a.s agr]
          isPre := a.isPre })
    | none => none
  | "AdvAP", [ap, adv] =>
    match ap.asAP?, adv.asAdv? with
    | some a, some ad =>
      some (.ap
        { s := fun agr => joinWords [ad, a.s agr]
          isPre := a.isPre })
    | _, _ => none
  | "PositAdvAdj", [a] =>
    match a.asA? with
    | some adj => some (.adv (adj.s .AAdv))
    | none => none
  | "ComparAdvAdj", [cadv, a, np] =>
    match a.asA?, np.asNP? with
    | some adj, some n =>
      some (.adv (joinWords [renderValue cadv {}, adj.s (.AAdj .Comp .Nom), n.s .NPAcc]))
    | _, _ => none
  | "ComparAdvAdjS", [cadv, a, s] =>
    match a.asA?, s.asListS? with
    | some adj, some [txt] =>
      some (.adv (joinWords [renderValue cadv {}, adj.s (.AAdj .Comp .Nom), txt]))
    | _, _ => none
  | "AdAdv", [ada, adv] =>
    match adv.asAdv? with
    | some ad => some (.adv (joinWords [renderValue ada {}, ad]))
    | none => none
  | "PositAdAAdj", [a] =>
    match a.asA? with
    | some adj => some (.raw Category.AdA (adj.s .AAdv))
    | none => none
  | "SubjS", [subj, s] =>
    match subj.asSubj?, s.asListS? with
    | some sj, some [txt] => some (.adv (joinWords [sj.s, txt]))
    | _, _ => none
  | "AdnCAdv", [cadv] =>
    some (.raw Category.AdN (renderValue cadv {}))
  | "TEmpty", [] =>
    some (.raw Category.Text "")
  | "TFullStop", [phr, txt] =>
    let body := joinWords [renderValue txt {}, renderValue phr {}]
    some (.raw Category.Text (body ++ "."))
  | "TQuestMark", [phr, txt] =>
    let body := joinWords [renderValue txt {}, renderValue phr {}]
    some (.raw Category.Text (body ++ "?"))
  | "TExclMark", [phr, txt] =>
    let body := joinWords [renderValue txt {}, renderValue phr {}]
    some (.raw Category.Text (body ++ "!"))
  | "no_Utt", [] => some (.raw Category.Utt "no")
  | "yes_Utt", [] => some (.raw Category.Utt "yes")
  | "language_title_Utt", [] => some (.raw Category.Utt "language title")
  | "FunRP", [prep, np, rp] =>
    match prep.asPrep?, np.asNP?, rp.asRP? with
    | some p, some n, some r =>
      some (.rp
        { r with
            s := fun rc =>
              match rc with
              | .RPrep _ => joinWords [p.s, n.s (.NCase .Nom), r.s rc]
              | _ => r.s rc })
    | _, _, _ => none
  | "DetCN", [d, cn] =>
    match d.asDet?, cn.asCN? with
    | some det, some noun => some (.np (linDetCN det noun))
    | _, _ => none
  | "DetQuant", [q, num] =>
    match q.asQuant?, num.asNum? with
    | some qv, some nv =>
      let det : EnglishDet :=
        { s := if nv.n == .Pl then qv.sPl else qv.sSg
          n := nv.n
          isDef := qv.isDef }
      some (.det det)
    | _, _ => none
  | "DetQuantOrd", [q, num, ord] =>
    match q.asQuant?, num.asNum?, ord.asOrd? with
    | some qv, some nv, some ov =>
      let qtxt := if nv.n == .Pl then qv.sPl else qv.sSg
      let det : EnglishDet :=
        { s := joinWords [qtxt, ov.s]
          n := nv.n
          isDef := qv.isDef }
      some (.det det)
    | _, _, _ => none
  | "NumSg", [] => some (.num { n := .Sg, card := "" })
  | "NumPl", [] => some (.num { n := .Pl, card := "" })
  | "NumCard", [card] =>
    match card.asCard? with
    | some c =>
      let inferred : Number :=
        if c = "1" || c = "one" || c = "One" then .Sg else .Pl
      some (.num { n := inferred, card := decimalCardinalWords c })
    | none => none
  | "NumDigits", [digits] => some (.card (renderValue digits {}))
  | "NumDecimal", [dec] => some (.card (decimalCardinalWords (renderValue dec {})))
  | "NumNumeral", [num] => some (.card (renderValue num {}))
  | "num", [sub] => some (.card (renderValue sub {}))
  | "pot01", [] => some (.card "1")
  | "pot0", [digit] => some (.card (renderValue digit {}))
  | "pot0as1", [sub10] => some (.card (renderValue sub10 {}))
  | "pot110", [] => some (.card "10")
  | "pot111", [] => some (.card "11")
  | "pot1to19", [digit] =>
    match parseNatCard? (renderValue digit {}) with
    | some d => some (cardNat (10 + d))
    | none => none
  | "pot1", [digit] =>
    match parseNatCard? (renderValue digit {}) with
    | some d => some (cardNat (d * 10))
    | none => none
  | "pot1plus", [digit, sub10] =>
    match parseNatCard? (renderValue digit {}), parseNatCard? (renderValue sub10 {}) with
    | some d, some r => some (cardNat (d * 10 + r))
    | _, _ => none
  | "pot1as2", [sub100] => some (.card (renderValue sub100 {}))
  | "pot21", [] => some (.card "100")
  | "pot2", [sub10] =>
    match parseNatCard? (renderValue sub10 {}) with
    | some h => some (cardNat (h * 100))
    | none => none
  | "pot2plus", [sub10, sub100] =>
    match parseNatCard? (renderValue sub10 {}), parseNatCard? (renderValue sub100 {}) with
    | some h, some r => some (cardNat (h * 100 + r))
    | _, _ => none
  | "pot2as3", [sub1000] => some (.card (renderValue sub1000 {}))
  | "pot31", [] => some (.card "1000000")
  | "pot3", [sub1000] =>
    match parseNatCard? (renderValue sub1000 {}) with
    | some m => some (cardNat (m * 1000))
    | none => none
  | "pot3plus", [sub1000, sub1000b] =>
    match parseNatCard? (renderValue sub1000 {}), parseNatCard? (renderValue sub1000b {}) with
    | some m, some r => some (cardNat (m * 1000 + r))
    | _, _ => none
  | "pot3as4", [sub1000000] => some (.card (renderValue sub1000000 {}))
  | "pot3decimal", [dec] => some (.card (renderValue dec {}))
  | "pot41", [] => some (.card "1000000000")
  | "pot4", [sub1000] =>
    match parseNatCard? (renderValue sub1000 {}) with
    | some b => some (cardNat (b * 1000000))
    | none => none
  | "pot4plus", [sub1000, sub1000000] =>
    match parseNatCard? (renderValue sub1000 {}), parseNatCard? (renderValue sub1000000 {}) with
    | some b, some r => some (cardNat (b * 1000000 + r))
    | _, _ => none
  | "pot4as5", [sub1000000000] => some (.card (renderValue sub1000000000 {}))
  | "pot4decimal", [dec] => some (.card (renderValue dec {}))
  | "pot51", [] => some (.card "1000000000000")
  | "pot5", [sub1000] =>
    match parseNatCard? (renderValue sub1000 {}) with
    | some t => some (cardNat (t * 1000000000))
    | none => none
  | "pot5plus", [sub1000, sub1000000000] =>
    match parseNatCard? (renderValue sub1000 {}), parseNatCard? (renderValue sub1000000000 {}) with
    | some t, some r => some (cardNat (t * 1000000000 + r))
    | _, _ => none
  | "pot5decimal", [dec] => some (.card (renderValue dec {}))
  | "IDig", [dig] => some (.card (renderValue dig {}))
  | "IIDig", [dig, digs] => some (.card (renderValue dig {} ++ renderValue digs {}))
  | "PosDecimal", [digits] => some (.card (renderValue digits {}))
  | "NegDecimal", [digits] => some (.card ("-" ++ renderValue digits {}))
  | "IFrac", [dec, dig] => some (.card (renderValue dec {} ++ "." ++ renderValue dig {}))
  | "OrdDigits", [digits] =>
    let base := decimalCardinalWords (renderValue digits {})
    some (.ord { s := ordinalizeCardinal base })
  | "OrdNumeral", [num] =>
    let base := decimalCardinalWords (renderValue num {})
    some (.ord { s := ordinalizeCardinal base })
  | "OrdSuperl", [a] =>
    match a.asA? with
    | some adj => some (.ord { s := "most " ++ adj.s (.AAdj .Pos .Nom) })
    | none => none
  | "PossPron", [np] =>
    np.asNP? |>.map (fun p => .quant { sSg := p.s (.NCase .Gen), sPl := p.s (.NCase .Gen), isDef := true })
  | "PredetNP", [predet, np] =>
    np.asNP? |>.map (fun n => .np (prefixNP (renderValue predet {}) n))
  | "PPartNP", [np, v2] =>
    match np.asNP?, v2.asV2? with
    | some n, some vv => some (.np (suffixNP n (vv.toEnglishVerb.s .VPPart)))
    | _, _ => none
  | "AdvNP", [np, adv] =>
    match np.asNP?, adv.asAdv? with
    | some n, some a => some (.np (suffixNP n a))
    | _, _ => none
  | "ExtAdvNP", [np, adv] =>
    match np.asNP?, adv.asAdv? with
    | some n, some a => some (.np (suffixNP n a))
    | _, _ => none
  | "RelNP", [np, rs] =>
    match np.asNP?, rs.asRS? with
    | some n, some r => some (.np (suffixNP n (r.s n.agr)))
    | _, _ => none
  | "CountNP", [det, np] =>
    match det.asDet?, np.asNP? with
    | some d, some n =>
      some (.np
        { s := fun npc => joinWords [d.s, n.s npc]
          agr := agrFromNumber d.n })
    | _, _ => none
  | "QuantityNP", [dec, mu] =>
    some (.np (mkLiteralNP (joinWords [renderValue dec {}, renderValue mu {}])))
  | "MassNP", [cn] => cn.asCN? |>.map (fun x => .np (linMassNP x))
  | "UsePron", [np] => np.asNP? |>.map .np
  | "UsePN", [pn] =>
    match pn.asNP? with
    | some n => some (.np n)
    | none =>
      match pn with
      | .raw (.base "PN") s => some (.np (mkLiteralNP s))
      | _ => none
  | "DefArt", [] => some (.quant { sSg := "the", sPl := "the", isDef := true })
  | "IndefArt", [] => some (.quant { sSg := "a", sPl := "some", isDef := false })
  | "DetNP", [d] =>
    match d.asDet? with
    | some det =>
      some (.np { s := fun _ => det.s, agr := agrFromNumber det.n })
    | none => none
  | "AdjCN", [ap, cn] =>
    match ap.asAP?, cn.asCN? with
    | some a, some n => some (.cn (linAdjCN a n))
    | _, _ => none
  | "AdvCN", [cn, adv] =>
    match cn.asCN?, adv.asAdv? with
    | some n, some a => some (.cn (linAdvCN n a))
    | _, _ => none

  -- Adjective pipeline
  | "PositA", [a] => a.asA? |>.map (fun x => .ap (linPositA x))
  | "ComparA", [a, np] =>
    match a.asA?, np.asNP? with
    | some adj, some obj =>
      let base := linComparA adj
      let ap : EnglishAP := { s := fun agr => base.s agr ++ " than " ++ obj.s .NPAcc, isPre := true }
      some (.ap ap)
    | _, _ => none

  -- Verb pipeline
  | "UseV", [v] => v.asV? |>.map (fun x => .vp (predV x))
  | "ComplVV", [vv, vp] =>
    match vv.asV2Comp?, vp.asVP? with
    | some f, some comp =>
      if f.kind == .vp then some (.vp (applyCompVerb f (vpCompSurface comp))) else none
    | _, _ => none
  | "ComplVS", [vs, s] =>
    match vs.asV2Comp?, s.asListS? with
    | some f, some [txt] =>
      if f.kind == .s then some (.vp (applyCompVerb f txt)) else none
    | _, _ => none
  | "ComplVQ", [vq, qs] =>
    match vq.asV2Comp?, qs.asListS? with
    | some f, some [txt] =>
      if f.kind == .qs then some (.vp (applyCompVerb f txt)) else none
    | _, _ => none
  | "ComplVA", [va, ap] =>
    match va.asV2Comp?, ap.asAP? with
    | some f, some adj =>
      if f.kind == .ap then some (.vp (applyCompVerb f (adj.s (.AgP3Sg .Neutr)))) else none
    | _, _ => none
  | "PassV2", [v2] =>
    v2.asV2? |>.map (fun x => .vp (passiveVP x))
  | "SlashVV", [vv, vps] =>
    match vv.asV2Comp?, vps.asVPSlash? with
    | some f, some s =>
      if f.kind == .vp then
        let base := applyCompVerb f (vpCompSurface s.toEnglishVP)
        some (.vpslash { base with c2 := s.c2 })
      else none
    | _, _ => none
  | "SlashV2VNP", [v2v, np, vps] =>
    match v2v.asV2Comp?, np.asNP?, vps.asVPSlash? with
    | some f, some obj, some s =>
      if f.kind == .vp then
        let base0 := applyCompVerb f (vpCompSurface s.toEnglishVP)
        let objTxt := addCompPrep f.objPrep (obj.s .NPAcc)
        let base := { base0 with compl := fun _ => objTxt }
        some (.vpslash { base with c2 := s.c2 })
      else none
    | _, _, _ => none
  | "ExtAdvVP", [vp, adv] =>
    match vp.asVP?, adv.asAdv? with
    | some v, some a => some (.vp (advVP v a))
    | _, _ => none
  | "AdVVP", [vp, adv] =>
    match vp.asVP?, adv.asAdv? with
    | some v, some a => some (.vp (advVP v a))
    | _, _ => none
  | "ReflVP", [vps] =>
    vps.asVPSlash? |>.map (fun s => .vp (fillSlashPreservingBase s (mkLiteralNP "itself")))
  | "CompNP", [np] =>
    np.asNP? |>.map (fun n => .comp ⟨fun _ => n.s (.NCase .Nom)⟩)
  | "CompAP", [ap] =>
    ap.asAP? |>.map (fun a => .comp ⟨fun agr => a.s agr⟩)
  | "CompAdv", [adv] =>
    adv.asAdv? |>.map (fun a => .comp ⟨fun _ => a⟩)
  | "CompCN", [cn] =>
    cn.asCN? |>.map (fun n => .comp ⟨fun _ => n.s .Sg .Nom⟩)
  | "UseComp", [comp] =>
    comp.asComp? |>.map (fun c => .vp (copulaVP c.render))
  | "UseCopula", [] =>
    some (.vp (copulaVP (fun _ => "")))
  | "SlashV2a", [v2] => v2.asV2? |>.map (fun x => .vpslash (slashV2a x))
  | "AdvVPSlash", [vps, adv] =>
    match vps.asVPSlash?, adv.asAdv? with
    | some s, some a =>
      some (.vpslash { (advVP s.toEnglishVP a) with c2 := s.c2 })
    | _, _ => none
  | "AdVVPSlash", [vps, adv] =>
    match vps.asVPSlash?, adv.asAdv? with
    | some s, some a =>
      some (.vpslash { (advVP s.toEnglishVP a) with c2 := s.c2 })
    | _, _ => none
  | "VPSlashPrep", [vp, prep] =>
    match vp.asVP?, prep.asPrep? with
    | some v, some p => some (.vpslash { v with c2 := p.s })
    | _, _ => none
  | "Slash2V3", [v3, np] =>
    match v3.asV3?, np.asNP? with
    | some f, some obj =>
      let filled := addCompPrep f.c2 (obj.s .NPAcc)
      some (.vpslash (applyV3Slash f filled f.c3))
    | _, _ => none
  | "Slash3V3", [v3, np] =>
    match v3.asV3?, np.asNP? with
    | some f, some obj =>
      let filled := addCompPrep f.c3 (obj.s .NPAcc)
      let base : EnglishVP := { (predV f.verb) with adv := filled }
      some (.vpslash { base with c2 := f.c2 })
    | _, _ => none
  | "SlashV2V", [v2c, vp] =>
    match v2c.asV2Comp?, vp.asVP? with
    | some f, some comp =>
      if f.kind == .vp then some (.vpslash (applyV2CompSlash f (vpCompSurface comp))) else none
    | _, _ => none
  | "SlashV2S", [v2c, s] =>
    match v2c.asV2Comp?, s.asListS? with
    | some f, some [txt] =>
      if f.kind == .s then some (.vpslash (applyV2CompSlash f txt)) else none
    | _, _ => none
  | "SlashV2Q", [v2c, qs] =>
    match v2c.asV2Comp?, qs.asListS? with
    | some f, some [txt] =>
      if f.kind == .qs then some (.vpslash (applyV2CompSlash f txt)) else none
    | _, _ => none
  | "SlashV2A", [v2c, ap] =>
    match v2c.asV2Comp?, ap.asAP? with
    | some f, some adj =>
      if f.kind == .ap then
        let txt := adj.s (.AgP3Sg .Neutr)
        some (.vpslash (applyV2CompSlash f txt))
      else none
    | _, _ => none
  | "ComplSlash", [vps, np] =>
    match vps.asVPSlash?, np.asNP? with
    | some x, some y => some (.vp (fillSlashPreservingBase x y))
    | _, _ => none
  | "AdvVP", [vp, adv] =>
    match vp.asVP?, adv.asAdv? with
    | some v, some a => some (.vp (advVP v a))
    | _, _ => none
  | "ImpersCl", [vp] =>
    match vp.asVP? with
    | some v => some (.cls (mkClause "it" (.AgP3Sg .Neutr) v))
    | none => none
  | "GenericCl", [vp] =>
    match vp.asVP? with
    | some v => some (.cls (mkClause "one" (.AgP3Sg .Neutr) v))
    | none => none
  | "CleftNP", [np, rs] =>
    match np.asNP?, rs.asRS? with
    | some n, some r =>
      let txt := joinWords ["it is", n.s (.NCase .Nom), r.s n.agr]
      some (.cls (fixedClause txt))
    | _, _ => none
  | "CleftAdv", [adv, s] =>
    match adv.asAdv?, s.asListS? with
    | some a, some [txt] => some (.cls (fixedClause (joinWords ["it is", a, txt])))
    | _, _ => none
  | "ExistNP", [np] =>
    match np.asNP? with
    | some n =>
      let vp := copulaVP (fun _ => n.s (.NCase .Nom))
      some (.cls (mkClause "there" (.AgP3Sg .Neutr) vp))
    | none => none
  | "ExistIP", [ip] =>
    let txt := joinWords ["is there", renderValue ip { case := .Nom }]
    some (.qcl (fixedQClause txt))
  | "ExistNPAdv", [np, adv] =>
    match np.asNP?, adv.asAdv? with
    | some n, some a =>
      let txt := joinWords ["there is", n.s (.NCase .Nom), a]
      some (.cls (fixedClause txt))
    | _, _ => none
  | "ExistIPAdv", [ip, adv] =>
    match adv.asAdv? with
    | some a =>
      let txt := joinWords ["is there", renderValue ip { case := .Nom }, a]
      some (.qcl (fixedQClause txt))
    | none => none
  | "ProgrVP", [vp] =>
    match vp.asVP? with
    | some v =>
      let prog : EnglishVP :=
        { inf := joinWords [be_V.s .VInf, v.prpart]
          pres := fun agr =>
            joinWords
              [ (match agr with
                | .AgP3Sg _ => "is"
                | _ => "are")
              , v.prpart
              ]
          past := joinWords [be_V.s .VPast, v.prpart]
          ppart := joinWords [be_V.s .VPPart, v.prpart]
          prpart := joinWords [be_V.s .VPresPart, v.prpart]
          particle := ""
          compl := fun agr => joinWords [v.particle, v.compl agr]
          adv := v.adv }
      some (.vp prog)
    | none => none
  | "ImpPl1", [vp] =>
    match vp.asVP? with
    | some v => some (.raw Category.Utt (joinWords ["let us", vpCompSurface v]))
    | none => none
  | "ImpP3", [np, vp] =>
    match np.asNP?, vp.asVP? with
    | some n, some v =>
      some (.raw Category.Utt (joinWords ["let", n.s (.NCase .Nom), vpCompSurface v]))
    | _, _ => none
  | "SelfAdvVP", [vp] =>
    match vp.asVP? with
    | some v => some (.vp (advVP v "by itself"))
    | none => none
  | "SelfAdVVP", [vp] =>
    match vp.asVP? with
    | some v => some (.vp (advVP v "by itself"))
    | none => none
  | "SelfNP", [np] =>
    np.asNP? |>.map (fun n => .np (suffixNP n "self"))

  -- Clause/sentence pipeline
  | "PredVP", [np, vp] =>
    match np.asNP?, vp.asVP? with
    | some s, some v => some (.cls (linPredVP s v))
    | _, _ => none
  | "PredSCVP", [sc, vp] =>
    match sc.asListS?, vp.asVP? with
    | some [sTxt], some v =>
      some (.cls (mkClause sTxt (.AgP3Sg .Neutr) v))
    | _, _ => none
  | "SlashVP", [np, vps] =>
    match np.asNP?, vps.asVPSlash? with
    | some s, some v => some (.clslash (slashVP s v))
    | _, _ => none
  | "AdvSlash", [cls, adv] =>
    match cls.asClSlash?, adv.asAdv? with
    | some c, some a =>
      some (.clslash
        { c with
            s := fun t ant pol ord => joinWords [c.s t ant pol ord, a] })
    | _, _ => none
  | "SlashPrep", [cl, prep] =>
    match cl.asCl?, prep.asPrep? with
    | some c, some p =>
      some (.clslash
        { s := fun t ant pol ord => c.s t ant pol ord
          c2 := p.s })
    | _, _ => none
  | "QuestCl", [cl] => cl.asCl? |>.map .qcl
  | "QuestVP", [ip, vp] =>
    match vp.asVP? with
    | some v =>
      let ipTxt := renderValue ip { case := .Nom }
      let cl := mkClause ipTxt (.AgP3Sg .Neutr) v
      some (.qcl cl)
    | none => none
  | "QuestSlash", [ip, cls] =>
    match cls.asClSlash? with
    | some c =>
      let ipTxt := renderValue ip { case := .Nom }
      let qtxt := joinWords [ipTxt, c.s .Pres .Simul .CPos (.ODir true), c.c2]
      some (.qcl (fixedQClause qtxt))
    | none => none
  | "PiedPipingQuestSlash", [ip, cls] =>
    match cls.asClSlash? with
    | some c =>
      let ipTxt := renderValue ip { case := .Nom }
      let qtxt := joinWords [ipTxt, c.c2, c.s .Pres .Simul .CPos (.ODir true)]
      some (.qcl (fixedQClause qtxt))
    | none => none
  | "StrandQuestSlash", [ip, cls] =>
    match cls.asClSlash? with
    | some c =>
      let ipTxt := renderValue ip { case := .Nom }
      let qtxt := joinWords [ipTxt, c.s .Pres .Simul .CPos (.ODir true), c.c2]
      some (.qcl (fixedQClause qtxt))
    | none => none
  | "QuestIAdv", [iadv, cl] =>
    match cl.asCl? with
    | some c =>
      let advTxt := renderValue iadv {}
      let qtxt := joinWords [advTxt, c.s .Pres .Simul .CPos (.ODir true)]
      some (.qcl (fixedQClause qtxt))
    | none => none
  | "QuestIComp", [icomp, np] =>
    match np.asNP? with
    | some n =>
      let compTxt := renderValue icomp {}
      let qtxt := joinWords [compTxt, n.s (.NCase .Nom)]
      some (.qcl (fixedQClause qtxt))
    | none => none
  | "IdetCN", [idet, cn] =>
    match cn.asCN? with
    | some n =>
      let idetTxt := renderValue idet {}
      some (.raw Category.IP (joinWords [idetTxt, n.s .Sg .Nom]))
    | none => none
  | "IdetIP", [idet] =>
    some (.raw Category.IP (renderValue idet {}))
  | "AdvIP", [ip, adv] =>
    match adv.asAdv? with
    | some a => some (.raw Category.IP (joinWords [renderValue ip { case := .Nom }, a]))
    | none => none
  | "IdetQuant", [iquant, num] =>
    let qtxt := renderValue iquant {}
    let nTxt := renderValue num {}
    some (.raw Category.IDet (joinWords [qtxt, nTxt]))
  | "PrepIP", [prep, ip] =>
    match prep.asPrep? with
    | some p => some (.raw Category.IAdv (joinWords [p.s, renderValue ip { case := .Nom }]))
    | none => none
  | "AdvIAdv", [iadv, adv] =>
    match adv.asAdv? with
    | some a => some (.raw Category.IAdv (joinWords [renderValue iadv {}, a]))
    | none => none
  | "CompIAdv", [iadv] =>
    some (.raw Category.IComp (renderValue iadv {}))
  | "CompIP", [ip] =>
    some (.raw Category.IComp (renderValue ip { case := .Nom }))
  | "ICompAP", [ap] =>
    match ap.asAP? with
    | some a => some (.raw Category.IComp (a.s (.AgP3Sg .Neutr)))
    | none => none
  | "IAdvAdv", [adv] =>
    match adv.asAdv? with
    | some a => some (.raw Category.IAdv a)
    | none => none
  | "CompIQuant", [iquant] =>
    some (.raw Category.IComp (renderValue iquant {}))
  | "GenIP", [ip] =>
    let txt := renderValue ip { case := .Nom }
    some (.raw Category.IQuant (txt ++ "'s"))
  | "ExistS", [tmp, pol, np] =>
    match tmp.asTemp?, pol.asPol?, np.asNP? with
    | some t, some p, some n =>
      let vp := copulaVP (fun _ => n.s (.NCase .Nom))
      let cl := mkClause "there" (.AgP3Sg .Neutr) vp
      some (.raw Category.S (linUseCl t.tense t.ant p cl))
    | _, _, _ => none
  | "ExistNPQS", [tmp, pol, np] =>
    match tmp.asTemp?, pol.asPol?, np.asNP? with
    | some t, some p, some n =>
      let qcl := fixedQClause (joinWords ["there", n.s (.NCase .Nom)])
      some (.raw Category.QS (linQuestCl t.tense t.ant p qcl))
    | _, _, _ => none
  | "ExistIPQS", [tmp, pol, ip] =>
    match tmp.asTemp?, pol.asPol? with
    | some t, some p =>
      let qcl := fixedQClause (joinWords ["there", renderValue ip { case := .Nom }])
      some (.raw Category.QS (linQuestCl t.tense t.ant p qcl))
    | _, _ => none
  | "ComplSlashIP", [vps, ip] =>
    match vps.asVPSlash? with
    | some s =>
      let ipTxt := renderValue ip { case := .Nom }
      let qtxt := joinWords [ipTxt, s.toEnglishVP.inf, s.toEnglishVP.compl (.AgP3Sg .Neutr), s.toEnglishVP.adv]
      some (.qvp ⟨qtxt⟩)
    | none => none
  | "AdvQVP", [vp, iadv] =>
    match vp.asVP? with
    | some v =>
      let advTxt := renderValue iadv {}
      some (.qvp ⟨joinWords [advTxt, vpCompSurface v]⟩)
    | none => none
  | "AddAdvQVP", [qvp, iadv] =>
    match qvp.asQVP? with
    | some q =>
      let advTxt := renderValue iadv {}
      some (.qvp ⟨joinWords [q.s, advTxt]⟩)
    | none => none
  | "QuestQVP", [ip, qvp] =>
    match qvp.asQVP? with
    | some q =>
      let ipTxt := renderValue ip { case := .Nom }
      some (.qcl (fixedQClause (joinWords [ipTxt, q.s])))
    | none => none
  | "TTAnt", [t, a] =>
    match t, a with
    | .tense tt, .ant aa => some (.temp ⟨tt, aa⟩)
    | _, _ => none
  | "PPos", [] => some (.pol .CPos)
  | "PNeg", [] => some (.pol (.CNeg false))
  | "TPres", [] => some (.tense .Pres)
  | "TPast", [] => some (.tense .Past)
  | "TFut", [] => some (.tense .Fut)
  | "TCond", [] => some (.tense .Cond)
  | "ASimul", [] => some (.ant .Simul)
  | "AAnter", [] => some (.ant .Anter)
  | "ImpVP", [vp] =>
    match vp.asVP? with
    | some v => some (.raw Category.Imp (vpCompSurface v))
    | none => none
  | "AdvImp", [adv, imp] =>
    match adv.asAdv? with
    | some a => some (.raw Category.Imp (joinWords [a, renderValue imp {}]))
    | none => none
  | "EmbedS", [s] =>
    some (.raw Category.SC (renderValue s {}))
  | "EmbedQS", [qs] =>
    some (.raw Category.SC (renderValue qs {}))
  | "EmbedVP", [vp] =>
    match vp.asVP? with
    | some v => some (.raw Category.SC (vpCompSurface v))
    | none => none
  | "UseSlash", [tmp, pol, cls] =>
    match tmp.asTemp?, pol.asPol?, cls.asClSlash? with
    | some t, some p, some c =>
      some (.raw Category.SSlash (joinWords [c.s t.tense t.ant p (.ODir true), c.c2]))
    | _, _, _ => none
  | "SlashVS", [np, vs, sslash] =>
    match np.asNP?, vs.asV2Comp? with
    | some subj, some frame =>
      let subjTxt := subj.s (.NCase .Nom)
      let compTxt := renderValue sslash {}
      let vp := applyCompVerb frame compTxt
      let clauseTxt := mkClause subjTxt subj.agr vp |>.s .Pres .Simul .CPos (.ODir true)
      some (.clslash { s := fun _ _ _ _ => clauseTxt, c2 := "" })
    | _, _ => none
  | "AdvS", [adv, s] =>
    match adv.asAdv?, s.asListS? with
    | some a, some [txt] => some (.listS [joinWords [a, txt]])
    | _, _ => none
  | "ExtAdvS", [adv, s] =>
    match adv.asAdv?, s.asListS? with
    | some a, some [txt] => some (.listS [joinWords [a, txt]])
    | _, _ => none
  | "RelS", [s, rs] =>
    match s.asListS? with
    | some [txt] =>
      let rsTxt := renderValue rs {}
      some (.listS [joinWords [txt, rsTxt]])
    | _ => none
  | "UseCl", [tmp, pol, cl] =>
    match tmp.asTemp?, pol.asPol?, cl.asCl? with
    | some t, some p, some c => some (.raw Category.S (linUseCl t.tense t.ant p c))
    | _, _, _ => none
  | "UseQCl", [tmp, pol, qcl] =>
    match tmp.asTemp?, pol.asPol?, qcl.asQCl? with
    | some t, some p, some c => some (.raw Category.QS (linQuestCl t.tense t.ant p c))
    | _, _, _ => none
  | "MkVPS", [tmp, pol, vp] =>
    match tmp.asTemp?, pol.asPol?, vp.asVP? with
    | some t, some p, some v =>
      let cl := mkClause "it" (.AgP3Sg .Neutr) v
      some (.raw (.base "VPS") (cl.s t.tense t.ant p (.ODir true)))
    | _, _, _ => none
  | "ConjVPS", [cj, xs] =>
    match cj.asConj?, xs.asListVPS? with
    | some c, some ys => some (.raw (.base "VPS") (joinWithConj ys c.s2))
    | _, _ => none
  | "PredVPS", [np, vps] =>
    match np.asNP? with
    | some n => some (.listS [joinWords [n.s (.NCase .Nom), renderValue vps {}]])
    | none => none
  | "SQuestVPS", [np, vps] =>
    match np.asNP? with
    | some n => some (.raw Category.QS (joinWords [n.s (.NCase .Nom), renderValue vps {}]))
    | none => none
  | "QuestVPS", [ip, vps] =>
    some (.raw Category.QS (joinWords [renderValue ip { case := .Nom }, renderValue vps {}]))
  | "RelVPS", [rp, vps] =>
    some (.rs { s := fun _ => joinWords [renderValue rp {}, renderValue vps {}] })
  | "BaseVPS", [a, b] =>
    some (.listVPS [renderValue a {}, renderValue b {}])
  | "ConsVPS", [a, xs] =>
    match xs.asListVPS? with
    | some ys => some (.listVPS (renderValue a {} :: ys))
    | none => none
  | "MkVPI", [vp] =>
    match vp.asVP? with
    | some v => some (.raw (.base "VPI") (vpCompSurface v))
    | none => none
  | "ConjVPI", [cj, xs] =>
    match cj.asConj?, xs.asListVPI? with
    | some c, some ys => some (.raw (.base "VPI") (joinWithConj ys c.s2))
    | _, _ => none
  | "ComplVPIVV", [vv, vpi] =>
    match vv.asV2Comp? with
    | some f =>
      if f.kind == .vp then
        some (.vp (applyCompVerb f (renderValue vpi {})))
      else none
    | none => none
  | "BaseVPI", [a, b] =>
    some (.listVPI [renderValue a {}, renderValue b {}])
  | "ConsVPI", [a, xs] =>
    match xs.asListVPI? with
    | some ys => some (.listVPI (renderValue a {} :: ys))
    | none => none
  | "MkVPS2", [tmp, pol, vps] =>
    match tmp.asTemp?, pol.asPol?, vps.asVPSlash? with
    | some t, some p, some s =>
      let cl := mkClause "it" (.AgP3Sg .Neutr) s.toEnglishVP
      let txt := joinWords [cl.s t.tense t.ant p (.ODir true), s.c2]
      some (.raw (.base "VPS2") txt)
    | _, _, _ => none
  | "ConjVPS2", [cj, xs] =>
    match cj.asConj?, xs.asListVPS2? with
    | some c, some ys => some (.raw (.base "VPS2") (joinWithConj ys c.s2))
    | _, _ => none
  | "ComplVPS2", [vps2, np] =>
    match np.asNP? with
    | some n => some (.raw (.base "VPS") (joinWords [renderValue vps2 {}, n.s .NPAcc]))
    | none => none
  | "ReflVPS2", [vps2, rnp] =>
    some (.raw (.base "VPS") (joinWords [renderValue vps2 {}, renderValue rnp {}]))
  | "BaseVPS2", [a, b] =>
    some (.listVPS2 [renderValue a {}, renderValue b {}])
  | "ConsVPS2", [a, xs] =>
    match xs.asListVPS2? with
    | some ys => some (.listVPS2 (renderValue a {} :: ys))
    | none => none
  | "MkVPI2", [vps] =>
    match vps.asVPSlash? with
    | some s => some (.raw (.base "VPI2") (joinWords [s.toEnglishVP.inf, s.c2]))
    | none => none
  | "ConjVPI2", [cj, xs] =>
    match cj.asConj?, xs.asListVPI2? with
    | some c, some ys => some (.raw (.base "VPI2") (joinWithConj ys c.s2))
    | _, _ => none
  | "ComplVPI2", [vpi2, np] =>
    match np.asNP? with
    | some n => some (.raw (.base "VPI") (joinWords [renderValue vpi2 {}, n.s .NPAcc]))
    | none => none
  | "BaseVPI2", [a, b] =>
    some (.listVPI2 [renderValue a {}, renderValue b {}])
  | "ConsVPI2", [a, xs] =>
    match xs.asListVPI2? with
    | some ys => some (.listVPI2 (renderValue a {} :: ys))
    | none => none
  | "ConjComp", [cj, xs] =>
    match cj.asConj?, xs.asListComp? with
    | some c, some ys => some (.comp ⟨fun _ => joinWithConj ys c.s2⟩)
    | _, _ => none
  | "BaseComp", [a, b] =>
    some (.listComp [renderValue a {}, renderValue b {}])
  | "ConsComp", [a, xs] =>
    match xs.asListComp? with
    | some ys => some (.listComp (renderValue a {} :: ys))
    | none => none
  | "ConjImp", [cj, xs] =>
    match cj.asConj?, xs.asListImp? with
    | some c, some ys => some (.raw Category.Imp (joinWithConj ys c.s2))
    | _, _ => none
  | "BaseImp", [a, b] =>
    some (.listImp [renderValue a {}, renderValue b {}])
  | "ConsImp", [a, xs] =>
    match xs.asListImp? with
    | some ys => some (.listImp (renderValue a {} :: ys))
    | none => none
  | "MkSymb", [s] =>
    some (.raw (.base "Symb") (renderValue s {}))
  | "BaseSymb", [a, b] =>
    some (.listSymb [renderValue a {}, renderValue b {}])
  | "ConsSymb", [a, xs] =>
    match xs.asListSymb? with
    | some ys => some (.listSymb (renderValue a {} :: ys))
    | none => none
  | "SymbPN", [symb] =>
    some (.raw (.base "PN") (renderValue symb {}))
  | "IntPN", [i] =>
    some (.raw (.base "PN") (renderValue i {}))
  | "FloatPN", [f] =>
    some (.raw (.base "PN") (renderValue f {}))
  | "NumPN", [card] =>
    some (.raw (.base "PN") (renderValue card {}))
  | "CNNumNP", [cn, card] =>
    match cn.asCN? with
    | some n => some (.np (mkLiteralNP (joinWords [renderValue card {}, n.s .Sg .Nom])))
    | none => none
  | "CNIntNP", [cn, i] =>
    match cn.asCN? with
    | some n => some (.np (mkLiteralNP (joinWords [renderValue i {}, n.s .Sg .Nom])))
    | none => none
  | "CNSymbNP", [det, cn, syms] =>
    match det.asDet?, det.asQuant?, cn.asCN?, syms.asListSymb? with
    | some d, _, some n, some xs =>
      some (.np (mkLiteralNP (joinWords [d.s, n.s .Sg .Nom, joinWithConj xs "and"])))
    | none, some q, some n, some xs =>
      some (.np (mkLiteralNP (joinWords [q.sSg, n.s .Sg .Nom, joinWithConj xs "and"])))
    | _, _, _, _ => none
  | "SymbS", [symb] =>
    some (.listS [renderValue symb {}])
  | "SymbNum", [symb] =>
    some (.card (renderValue symb {}))
  | "SymbOrd", [symb] =>
    some (.ord { s := renderValue symb {} })

  -- Relative clauses
  | "IdRP", [] => some (.rp idRP)
  | "RelCl", [cl] =>
    match cl.asCl? with
    | some c =>
      some (.rcl
        { s := fun t ant pol _ => "that " ++ c.s t ant pol (.ODir true) })
    | none => none
  | "RelVP", [rp, vp] =>
    match rp.asRP?, vp.asVP? with
    | some r, some v => some (.rcl (relVP r v))
    | _, _ => none
  | "RelSlash", [rp, cls] =>
    match rp.asRP?, cls.asClSlash? with
    | some r, some c => some (.rcl (relSlash r c))
    | _, _ => none
  | "PiedPipingRelSlash", [rp, cls] =>
    match rp.asRP?, cls.asClSlash? with
    | some r, some c =>
      let rtxt := r.s (.RC .Neutr (.NCase .Nom))
      let txt := joinWords [rtxt, c.c2, c.s .Pres .Simul .CPos (.ODir true)]
      some (.rcl { s := fun _ _ _ _ => txt })
    | _, _ => none
  | "StrandRelSlash", [rp, cls] =>
    match rp.asRP?, cls.asClSlash? with
    | some r, some c =>
      let rtxt := r.s (.RC .Neutr (.NCase .Nom))
      let txt := joinWords [rtxt, c.s .Pres .Simul .CPos (.ODir true), c.c2]
      some (.rcl { s := fun _ _ _ _ => txt })
    | _, _ => none
  | "EmptyRelSlash", [cls] =>
    match cls.asClSlash? with
    | some c =>
      let txt :=
        if c.c2 == "" then
          joinWords ["that", c.s .Pres .Simul .CPos (.ODir true)]
        else
          joinWords ["that", c.s .Pres .Simul .CPos (.ODir true), c.c2]
      some (.rcl { s := fun _ _ _ _ => txt })
    | none => none
  | "GenRP", [num, cn] =>
    match cn.asCN? with
    | some n =>
      let q := renderValue num {}
      let core := if q == "" then n.s .Sg .Nom else joinWords [q, n.s .Sg .Nom]
      some (.rp { s := fun _ => joinWords ["whose", core], a := .RNoAg })
    | none => none
  | "UseRCl", [tmp, pol, rcl] =>
    match tmp.asTemp?, pol.asPol?, rcl.asRCl? with
    | some t, some p, some r => some (.rs (useRCl t.tense t.ant p r))
    | _, _, _ => none
  | "RelCN", [cn, rs] =>
    match cn.asCN?, rs.asRS? with
    | some n, some r => some (.cn (relCN n r))
    | _, _ => none

  -- Phrase/Utt layer
  | "NoPConj", [] => some (.raw Category.PConj "")
  | "PConjConj", [cj] =>
    match cj.asConj? with
    | some c => some (.raw Category.PConj c.s2)
    | none => none
  | "NoVoc", [] => some (.raw Category.Voc "")
  | "VocNP", [np] =>
    match np.asNP? with
    | some n => some (.raw Category.Voc (n.s (.NCase .Nom)))
    | none => none
  | "UttS", [s] =>
    match s.asListS? with
    | some [txt] => some (.raw Category.Utt txt)
    | _ => none
  | "UttQS", [qs] =>
    match qs.asListS? with
    | some [txt] => some (.raw Category.Utt txt)
    | _ => none
  | "UttImpSg", [pol, imp] =>
    match pol.asPol? with
    | some .CPos => some (.raw Category.Utt (renderValue imp {}))
    | some (.CNeg _) => some (.raw Category.Utt (joinWords ["do not", renderValue imp {}]))
    | none => none
  | "UttImpPl", [pol, imp] =>
    match pol.asPol? with
    | some .CPos => some (.raw Category.Utt (renderValue imp {}))
    | some (.CNeg _) => some (.raw Category.Utt (joinWords ["do not", renderValue imp {}]))
    | none => none
  | "UttImpPol", [pol, imp] =>
    match pol.asPol? with
    | some .CPos => some (.raw Category.Utt (renderValue imp {}))
    | some (.CNeg _) => some (.raw Category.Utt (joinWords ["do not", renderValue imp {}]))
    | none => none
  | "UttIP", [ip] => some (.raw Category.Utt (renderValue ip { case := .Nom }))
  | "UttIAdv", [iadv] => some (.raw Category.Utt (renderValue iadv {}))
  | "UttNP", [np] =>
    match np.asNP? with
    | some n => some (.raw Category.Utt (n.s (.NCase .Nom)))
    | none => none
  | "UttAdv", [adv] =>
    match adv.asAdv? with
    | some a => some (.raw Category.Utt a)
    | none => none
  | "UttVP", [vp] =>
    match vp.asVP? with
    | some v => some (.raw Category.Utt (vpCompSurface v))
    | none => none
  | "UttCN", [cn] =>
    match cn.asCN? with
    | some n => some (.raw Category.Utt (n.s .Sg .Nom))
    | none => none
  | "UttCard", [card] =>
    match card.asCard? with
    | some c => some (.raw Category.Utt c)
    | none => some (.raw Category.Utt (renderValue card {}))
  | "UttAP", [ap] =>
    match ap.asAP? with
    | some a => some (.raw Category.Utt (a.s (.AgP3Sg .Neutr)))
    | none => none
  | "UttInterj", [interj] => some (.raw Category.Utt (renderValue interj {}))
  | "GenNP", [np] =>
    match np.asNP? with
    | some n =>
      let g := n.s (.NCase .Gen)
      some (.quant { sSg := g, sPl := g, isDef := true })
    | none => none
  | "GenModNP", [num, np, cn] =>
    match np.asNP?, cn.asCN? with
    | some n, some c =>
      let q := renderValue num {}
      let txt := joinWords [q, n.s (.NCase .Nom), c.s .Sg .Nom]
      some (.np (mkLiteralNP txt))
    | _, _ => none
  | "GenModIP", [num, ip, cn] =>
    match cn.asCN? with
    | some c =>
      let txt := joinWords [renderValue num {}, renderValue ip { case := .Nom }, c.s .Sg .Nom]
      some (.raw Category.IP txt)
    | none => none
  | "CompBareCN", [cn] =>
    cn.asCN? |>.map (fun n => .comp ⟨fun _ => n.s .Sg .Nom⟩)
  | "ProDrop", [pron] =>
    pron.asNP? |>.map .np
  | "PrepCN", [prep, cn] =>
    match prep.asPrep?, cn.asCN? with
    | some p, some n => some (.adv (joinWords [p.s, n.s .Sg .Nom]))
    | _, _ => none
  | "FocusObj", [np, sslash] =>
    match np.asNP? with
    | some n => some (.raw Category.Utt (joinWords [n.s (.NCase .Nom), renderValue sslash {}]))
    | none => none
  | "FocusAdv", [adv, s] =>
    match adv.asAdv?, s.asListS? with
    | some a, some [txt] => some (.raw Category.Utt (joinWords [a, txt]))
    | _, _ => none
  | "FocusAdV", [adv, s] =>
    match adv.asAdv?, s.asListS? with
    | some a, some [txt] => some (.raw Category.Utt (joinWords [a, txt]))
    | _, _ => none
  | "FocusAP", [ap, np] =>
    match ap.asAP?, np.asNP? with
    | some a, some n => some (.raw Category.Utt (joinWords [a.s n.agr, n.s (.NCase .Nom)]))
    | _, _ => none
  | "PresPartAP", [vp] =>
    match vp.asVP? with
    | some v =>
      some (.ap
        { s := fun agr => joinWords [v.prpart, v.compl agr, v.adv]
          isPre := false })
    | none => none
  | "EmbedPresPart", [vp] =>
    match vp.asVP? with
    | some v =>
      some (.raw Category.SC (joinWords [v.prpart, v.compl (.AgP3Sg .Neutr), v.adv]))
    | none => none
  | "PastPartAP", [vps] =>
    match vps.asVPSlash? with
    | some s =>
      some (.ap
        { s := fun agr => joinWords [s.toEnglishVP.ppart, s.toEnglishVP.compl agr, s.toEnglishVP.adv, s.c2]
          isPre := false })
    | none => none
  | "PastPartAgentAP", [vps, np] =>
    match vps.asVPSlash?, np.asNP? with
    | some s, some n =>
      some (.ap
        { s := fun agr =>
            joinWords
              [ s.toEnglishVP.ppart
              , s.toEnglishVP.compl agr
              , s.toEnglishVP.adv
              , s.c2
              , "by"
              , n.s .NPAcc
              ]
          isPre := false })
    | _, _ => none
  | "PassVPSlash", [vps] =>
    match vps.asVPSlash? with
    | some s =>
      let base := s.toEnglishVP
      let pass : EnglishVP :=
        { inf := joinWords [be_V.s .VInf, base.ppart]
          pres := fun agr =>
            joinWords
              [ (match agr with
                | .AgP3Sg _ => "is"
                | _ => "are")
              , base.ppart
              ]
          past := joinWords [be_V.s .VPast, base.ppart]
          ppart := joinWords [be_V.s .VPPart, base.ppart]
          prpart := joinWords [be_V.s .VPresPart, base.ppart]
          particle := ""
          compl := base.compl
          adv := base.adv }
      some (.vp pass)
    | none => none
  | "PassAgentVPSlash", [vps, np] =>
    match vps.asVPSlash?, np.asNP? with
    | some s, some n =>
      let base := s.toEnglishVP
      let pass : EnglishVP :=
        { inf := joinWords [be_V.s .VInf, base.ppart]
          pres := fun agr =>
            joinWords
              [ (match agr with
                | .AgP3Sg _ => "is"
                | _ => "are")
              , base.ppart
              ]
          past := joinWords [be_V.s .VPast, base.ppart]
          ppart := joinWords [be_V.s .VPPart, base.ppart]
          prpart := joinWords [be_V.s .VPresPart, base.ppart]
          particle := ""
          compl := base.compl
          adv := joinWords [base.adv, "by", n.s .NPAcc] }
      some (.vp pass)
    | _, _ => none
  | "NominalizeVPSlashNP", [vps, np] =>
    match vps.asVPSlash?, np.asNP? with
    | some s, some n =>
      let txt := joinWords ["the", s.toEnglishVP.ppart, s.c2, n.s .NPAcc]
      some (.np (mkLiteralNP txt))
    | _, _ => none
  | "PhrUtt", [pconj, utt, voc] =>
    let ptxt := renderValue pconj {}
    let utxt := renderValue utt {}
    let vtxt := renderValue voc {}
    some (.raw Category.Phr (joinWords [ptxt, utxt, vtxt]))

  -- Adverbial PP
  | "PrepNP", [prep, np] =>
    match prep.asPrep?, np.asNP? with
    | some p, some n => some (.adv (linPrepNP p n))
    | _, _ => none

  -- Subordination over sentence strings
  | "SSubjS", [s1, subj, s2] =>
    match s1.asListS?, subj.asSubj?, s2.asListS? with
    | some [a], some sj, some [b] => some (.raw Category.S (linSSubjS a sj b))
    | _, _, _ => none

  -- Coordination lists + conjunction for NP/CN/AP/S
  | "BaseNP", [a, b] =>
    match a.asNP?, b.asNP? with
    | some x, some y => some (.listNP [x, y])
    | _, _ => none
  | "ConsNP", [a, xs] =>
    match a.asNP?, xs.asListNP? with
    | some x, some ys => some (.listNP (x :: ys))
    | _, _ => none
  | "ConjNP", [cj, xs] =>
    match cj.asConj?, xs.asListNP? with
    | some c, some ys =>
      let txts := ys.map (fun np => np.s (.NCase .Nom))
      some (.np { s := fun _ => joinWithConj txts c.s2, agr := agrFromNumber c.n })
    | _, _ => none

  | "BaseCN", [a, b] =>
    match a.asCN?, b.asCN? with
    | some x, some y => some (.listCN [x, y])
    | _, _ => none
  | "ConsCN", [a, xs] =>
    match a.asCN?, xs.asListCN? with
    | some x, some ys => some (.listCN (x :: ys))
    | _, _ => none
  | "ConjCN", [cj, xs] =>
    match cj.asConj?, xs.asListCN? with
    | some c, some ys =>
      let cn : EnglishCN :=
        { s := fun n cas => joinWithConj (ys.map (fun x => x.s n cas)) c.s2
          g := .Neutr }
      some (.cn cn)
    | _, _ => none

  | "BaseRS", [a, b] =>
    match a.asRS?, b.asRS? with
    | some x, some y => some (.listRS [x, y])
    | _, _ => none
  | "ConsRS", [a, xs] =>
    match a.asRS?, xs.asListRS? with
    | some x, some ys => some (.listRS (x :: ys))
    | _, _ => none
  | "ConjRS", [cj, xs] =>
    match cj.asConj?, xs.asListRS? with
    | some c, some ys =>
      some (.rs { s := fun agr => joinWithConj (ys.map (fun rs => rs.s agr)) c.s2 })
    | _, _ => none

  | "BaseAdv", [a, b] =>
    match a.asAdv?, b.asAdv? with
    | some x, some y => some (.listAdv [x, y])
    | _, _ => none
  | "ConsAdv", [a, xs] =>
    match a.asAdv?, xs.asListAdv? with
    | some x, some ys => some (.listAdv (x :: ys))
    | _, _ => none
  | "ConjAdv", [cj, xs] =>
    match cj.asConj?, xs.asListAdv? with
    | some c, some ys => some (.adv (joinWithConj ys c.s2))
    | _, _ => none

  | "BaseAdV", [a, b] =>
    match a.asAdv?, b.asAdv? with
    | some x, some y => some (.listAdV [x, y])
    | _, _ => none
  | "ConsAdV", [a, xs] =>
    match a.asAdv?, xs.asListAdV? with
    | some x, some ys => some (.listAdV (x :: ys))
    | _, _ => none
  | "ConjAdV", [cj, xs] =>
    match cj.asConj?, xs.asListAdV? with
    | some c, some ys => some (.raw Category.AdV (joinWithConj ys c.s2))
    | _, _ => none

  | "BaseIAdv", [a, b] =>
    match a.asAdv?, b.asAdv? with
    | some x, some y => some (.listIAdv [x, y])
    | _, _ => none
  | "ConsIAdv", [a, xs] =>
    match a.asAdv?, xs.asListIAdv? with
    | some x, some ys => some (.listIAdv (x :: ys))
    | _, _ => none
  | "ConjIAdv", [cj, xs] =>
    match cj.asConj?, xs.asListIAdv? with
    | some c, some ys => some (.raw Category.IAdv (joinWithConj ys c.s2))
    | _, _ => none

  | "BaseAP", [a, b] =>
    match a.asAP?, b.asAP? with
    | some x, some y => some (.listAP [x, y])
    | _, _ => none
  | "ConsAP", [a, xs] =>
    match a.asAP?, xs.asListAP? with
    | some x, some ys => some (.listAP (x :: ys))
    | _, _ => none
  | "ConjAP", [cj, xs] =>
    match cj.asConj?, xs.asListAP? with
    | some c, some ys =>
      let ap : EnglishAP :=
        { s := fun agr => joinWithConj (ys.map (fun x => x.s agr)) c.s2
          isPre := true }
      some (.ap ap)
    | _, _ => none

  | "BaseDAP", [a, b] =>
    match a.asDet?, b.asDet? with
    | some x, some y => some (.listDet [x, y])
    | _, _ => none
  | "ConsDAP", [a, xs] =>
    match a.asDet?, xs.asListDet? with
    | some x, some ys => some (.listDet (x :: ys))
    | _, _ => none
  | "ConjDet", [cj, xs] =>
    match cj.asConj?, xs.asListDet? with
    | some c, some ys =>
      let isDef := ys.all (fun d => d.isDef)
      some (.det { s := joinWithConj (ys.map (fun d => d.s)) c.s2, n := c.n, isDef := isDef })
    | _, _ => none

  | "BaseS", [a, b] =>
    match a.asListS?, b.asListS? with
    | some [x], some [y] => some (.listS [x, y])
    | _, _ => none
  | "ConsS", [a, xs] =>
    match a.asListS?, xs.asListS? with
    | some [x], some ys => some (.listS (x :: ys))
    | _, _ => none
  | "ConjS", [cj, xs] =>
    match cj.asConj?, xs.asListS? with
    | some c, some ys => some (.raw Category.S (joinWithConj ys c.s2))
    | _, _ => none

  | _, _ => none

partial def evalNode (env : EnglishLinEnv) : AbstractNode → EngValue
  | .leaf name cat => evalLeafValue env name cat
  | .apply f args =>
    let argVals := args.map (evalNode env)
    match dispatchApply f argVals with
    | some v => v
    | none =>
      if argVals.isEmpty then
        evalLeafValue env f.name (FunctionSig.resultCategory f.type)
      else
        .raw (FunctionSig.resultCategory f.type) (fallbackAppString f.name argVals)

/-! ## Public Linearization API -/

/-- Linearize an abstract tree to English.
Uses typed evaluation with default sentence parameters for clause-level nodes. -/
def linearizeTree (env : EnglishLinEnv) (node : AbstractNode) (c : Case) (n : Number) : String :=
  renderValue (evalNode env node) { case := c, number := n }

/-- Build an English `NodeLinearize` instance for abstract equivalence. -/
def englishLinearize (env : EnglishLinEnv) : Abstract.NodeLinearize EnglishParams :=
  fun node params => linearizeTree env node params.case params.number

/-! ## Bridge Theorems -/

/-- NodeEquiv under English linearization implies case/number string equality. -/
theorem nodeEquiv_implies_string_eq (env : EnglishLinEnv) (n1 n2 : AbstractNode) :
    Abstract.NodeEquiv (englishLinearize env) n1 n2 →
    ∀ (c : Case) (num : Number),
      linearizeTree env n1 c num = linearizeTree env n2 c num := by
  intro h c num
  exact h ⟨c, num⟩

/-- Leaf linearization respects explicit noun lookup. -/
theorem linearizeLeaf_found (env : EnglishLinEnv) (name : String) (cn : EnglishNoun)
    (h : env.lookupCN name = some cn) (c : Case) (n : Number) :
    linearizeLeaf env name c n = cn.s n c := by
  simp [linearizeLeaf, h]

/-- Leaf linearization falls back to the literal name when unresolved. -/
theorem linearizeLeaf_notFound (env : EnglishLinEnv) (name : String)
    (hCN : env.lookupCN name = none) (hN : env.lookupN name = none)
    (c : Case) (n : Number) :
    linearizeLeaf env name c n = name := by
  simp [linearizeLeaf, hCN, hN]

/-! ## Extended Sentence Parameters -/

structure EnglishSentenceParams where
  tense : Tense
  anteriority : Anteriority
  polarity : CPolarity
  order : Order
  deriving DecidableEq, Repr, Inhabited

/-- Full English linearization with sentence-level parameters.
The `mkVP` fallback is used only for unresolved leaves. -/
def englishSentenceLinearize (env : EnglishLinEnv)
    (mkVP : String → EnglishVP)
    (node : AbstractNode) (sp : EnglishSentenceParams) : String :=
  match evalNode env node with
  | EngValue.cls cl => cl.s sp.tense sp.anteriority sp.polarity sp.order
  | EngValue.qcl cl => cl.s sp.tense sp.anteriority sp.polarity .OQuest
  | EngValue.vp vp =>
    let cl := mkClause "it" (.AgP3Sg .Neutr) vp
    cl.s sp.tense sp.anteriority sp.polarity sp.order
  | EngValue.raw _ txt => txt
  | EngValue.noun n =>
    let np := linDetCN theDefArt n
    let cl := linPredVP np (mkVP (n.s .Sg .Nom))
    cl.s sp.tense sp.anteriority sp.polarity sp.order
  | v =>
    renderValue v
      { case := .Nom
        number := .Sg
        tense := sp.tense
        ant := sp.anteriority
        pol := sp.polarity
        order := sp.order }

/-! ## Coverage Diagnostics -/

/-- Function names with explicit typed semantics in `dispatchApply`. -/
def explicitApplyFunctionNames : List String :=
  [ "UseN", "AdNum", "OrdNumeralSuperl", "ComplN2", "ComplN3", "UseN2", "Use2N3", "Use3N3"
  , "SentCN", "ApposCN", "PossNP", "PartNP", "AdjDAP", "DetDAP"
  , "ComplA2", "ReflA2", "UseA2", "UseComparA", "CAdvAP", "AdjOrd", "SentAP", "AdAP", "AdvAP"
  , "PositAdvAdj", "ComparAdvAdj", "ComparAdvAdjS", "AdAdv", "PositAdAAdj", "SubjS", "AdnCAdv"
  , "TEmpty", "TFullStop", "TQuestMark", "TExclMark", "no_Utt", "yes_Utt", "language_title_Utt", "FunRP"
  , "DetCN", "DetQuant", "DetQuantOrd", "PredetNP", "PPartNP", "AdvNP", "ExtAdvNP"
  , "RelNP", "CountNP", "QuantityNP", "MassNP", "UsePron", "UsePN", "AdjCN", "AdvCN"
  , "DefArt", "IndefArt", "DetNP", "NumSg", "NumPl", "NumCard", "NumDigits", "NumDecimal"
  , "NumNumeral", "num", "pot01", "pot0", "pot0as1", "pot110", "pot111", "pot1to19", "pot1"
  , "pot1plus", "pot1as2", "pot21", "pot2", "pot2plus", "pot2as3", "pot31", "pot3", "pot3plus"
  , "pot3as4", "pot3decimal", "pot41", "pot4", "pot4plus", "pot4as5", "pot4decimal", "pot51"
  , "pot5", "pot5plus", "pot5decimal", "IDig", "IIDig", "PosDecimal", "NegDecimal", "IFrac"
  , "OrdDigits", "OrdNumeral", "OrdSuperl", "PossPron"
  , "PositA", "ComparA", "UseV", "ComplVV", "ComplVS", "ComplVQ", "ComplVA", "PassV2"
  , "SlashVV", "SlashV2VNP", "ReflVP", "ExtAdvVP", "AdVVP", "CompNP", "CompAP", "CompAdv", "CompCN"
  , "UseComp", "UseCopula", "SlashV2a", "AdvVPSlash", "AdVVPSlash", "VPSlashPrep"
  , "Slash2V3", "Slash3V3", "SlashV2V", "SlashV2S", "SlashV2Q", "SlashV2A", "ComplSlash", "AdvVP"
  , "ImpersCl", "GenericCl", "CleftNP", "CleftAdv", "ExistNP", "ExistIP", "ExistNPAdv", "ExistIPAdv"
  , "ProgrVP", "ImpPl1", "ImpP3", "SelfAdvVP", "SelfAdVVP", "SelfNP"
  , "PredVP", "PredSCVP", "SlashVP", "AdvSlash", "SlashPrep"
  , "QuestCl", "QuestVP", "QuestSlash", "PiedPipingQuestSlash", "StrandQuestSlash"
  , "QuestIAdv", "QuestIComp", "IdetCN", "IdetIP", "AdvIP", "IdetQuant"
  , "PrepIP", "AdvIAdv", "CompIAdv", "CompIP", "ICompAP", "IAdvAdv", "CompIQuant", "GenIP"
  , "ExistS", "ExistNPQS", "ExistIPQS", "ComplSlashIP", "AdvQVP", "AddAdvQVP", "QuestQVP"
  , "TTAnt", "PPos", "PNeg", "TPres", "TPast", "TFut"
  , "TCond", "ASimul", "AAnter", "ImpVP", "AdvImp", "EmbedS", "EmbedQS", "EmbedVP", "UseSlash", "SlashVS"
  , "AdvS", "ExtAdvS", "RelS", "UseCl", "UseQCl"
  , "IdRP", "RelCl", "RelVP", "RelSlash", "PiedPipingRelSlash", "StrandRelSlash", "EmptyRelSlash"
  , "UseRCl", "RelCN", "GenRP", "PrepNP", "SSubjS"
  , "NoPConj", "PConjConj", "NoVoc", "VocNP", "PhrUtt", "UttS", "UttQS", "UttImpSg", "UttImpPl", "UttImpPol"
  , "UttIP", "UttIAdv", "UttNP", "UttAdv", "UttVP", "UttCN", "UttCard", "UttAP", "UttInterj"
  , "GenNP", "GenModNP", "GenModIP", "CompBareCN", "ProDrop", "PrepCN"
  , "FocusObj", "FocusAdv", "FocusAdV", "FocusAP", "PresPartAP", "EmbedPresPart", "PastPartAP"
  , "PastPartAgentAP", "PassVPSlash", "PassAgentVPSlash", "NominalizeVPSlashNP"
  , "MkVPS", "ConjVPS", "PredVPS", "SQuestVPS", "QuestVPS", "RelVPS", "BaseVPS", "ConsVPS"
  , "MkVPI", "ConjVPI", "ComplVPIVV", "BaseVPI", "ConsVPI"
  , "MkVPS2", "ConjVPS2", "ComplVPS2", "ReflVPS2", "BaseVPS2", "ConsVPS2"
  , "MkVPI2", "ConjVPI2", "ComplVPI2", "BaseVPI2", "ConsVPI2"
  , "ConjComp", "BaseComp", "ConsComp", "ConjImp", "BaseImp", "ConsImp"
  , "MkSymb", "BaseSymb", "ConsSymb", "SymbPN", "IntPN", "FloatPN", "NumPN"
  , "CNNumNP", "CNIntNP", "CNSymbNP", "SymbS", "SymbNum", "SymbOrd"
  , "BaseNP", "ConsNP", "ConjNP", "BaseCN", "ConsCN", "ConjCN", "BaseRS", "ConsRS", "ConjRS"
  , "BaseAdv", "ConsAdv", "ConjAdv", "BaseAdV", "ConsAdV", "ConjAdV"
  , "BaseIAdv", "ConsIAdv", "ConjIAdv", "BaseDAP", "ConsDAP", "ConjDet"
  , "BaseAP", "ConsAP", "ConjAP", "BaseS", "ConsS", "ConjS" ]

/-- Result categories that are typed by `evalLeafValue` (not raw fallback). -/
def typedLeafResultCategories : List Category :=
  [ Category.base "N", Category.base "CN", Category.base "N2", Category.base "N3"
  , Category.base "A", Category.base "A2", Category.base "Predet", Category.base "AdA", Category.base "AdN", Category.base "CAdv"
  , Category.base "V", Category.base "V2"
  , Category.base "VV", Category.base "VS", Category.base "VQ", Category.base "VA"
  , Category.base "V3", Category.base "V2V", Category.base "V2S", Category.base "V2Q", Category.base "V2A"
  , Category.base "Quant", Category.base "Num", Category.base "Card", Category.base "Ord"
  , Category.base "Digit", Category.base "Dig", Category.base "Digits", Category.base "Decimal", Category.base "Numeral"
  , Category.base "Sub10", Category.base "Sub100", Category.base "Sub1000", Category.base "Sub1000000"
  , Category.base "Sub1000000000", Category.base "Sub1000000000000"
  , Category.base "Det", Category.base "DAP", Category.base "Pron", Category.base "NP"
  , Category.base "Adv", Category.base "AdV", Category.base "IAdv"
  , Category.base "Text"
  , Category.base "IP", Category.base "IComp", Category.base "IDet", Category.base "IQuant", Category.base "RP"
  , Category.base "Prep", Category.base "Conj", Category.base "Subj", Category.base "Interj"
  , Category.base "PConj", Category.base "Voc"
  , Category.base "Tense", Category.base "Ant", Category.base "Pol" ]

/-- Zero-arity constructors handled by typed leaf linearization. -/
def typedLeafFunctionNames : List String :=
  FunctionSig.allFunctions.foldl
    (fun acc f =>
      if f.arity = 0 && typedLeafResultCategories.contains (FunctionSig.resultCategory f.type) then
        f.name :: acc
      else
        acc)
    []

/-- Complete typed-handler set: explicit apply handlers + typed leaf handlers. -/
def explicitlyHandledFunctionNames : List String :=
  (explicitApplyFunctionNames ++ typedLeafFunctionNames).eraseDups

/-- Non-lexical GF abstract functions (core grammar constructors only).
Excludes lexicon entries to provide a meaningful grammar-coverage signal. -/
def nonLexicalFunctionNames : List String :=
  ( FunctionSig.allCoreFunctions ++ FunctionSig.adverbFunctions ++ FunctionSig.tenseFunctions
    ++ FunctionSig.textFunctions ++ FunctionSig.idiomFunctions ++ FunctionSig.numeralFunctions
    ++ FunctionSig.structuralFunctions ++ FunctionSig.extendFunctions
    ++ FunctionSig.constructionFunctions ++ FunctionSig.symbolFunctions
  ).map (·.name)

/-- Explicitly handled non-lexical function names. -/
def explicitlyHandledNonLexicalFunctionNames : List String :=
  nonLexicalFunctionNames.filter (fun name => explicitlyHandledFunctionNames.contains name)

/-- Non-lexical function names still without explicit typed handlers. -/
def uncoveredNonLexicalFunctionNames : List String :=
  nonLexicalFunctionNames.filter (fun name => !(explicitlyHandledFunctionNames.contains name))

/-- Number of GF abstract functions with explicit typed handlers. -/
def explicitCoverageCount : Nat :=
  FunctionSig.allFunctions.foldl
    (fun acc f => if explicitlyHandledFunctionNames.contains f.name then acc + 1 else acc)
    0

/-- Number of functions with explicit `dispatchApply` handlers. -/
def explicitApplyCoverageCount : Nat :=
  FunctionSig.allFunctions.foldl
    (fun acc f => if explicitApplyFunctionNames.contains f.name then acc + 1 else acc)
    0

/-- Number of zero-arity functions covered by typed leaf linearization. -/
def typedLeafCoverageCount : Nat :=
  FunctionSig.allFunctions.foldl
    (fun acc f => if typedLeafFunctionNames.contains f.name then acc + 1 else acc)
    0

/-- Number of names that are both explicit apply handlers and typed leaf handlers. -/
def applyLeafOverlapCount : Nat :=
  explicitApplyFunctionNames.foldl
    (fun acc name => if typedLeafFunctionNames.contains name then acc + 1 else acc)
    0

/-- Number of non-lexical GF abstract functions. -/
def nonLexicalFunctionCount : Nat :=
  nonLexicalFunctionNames.length

/-- Number of non-lexical functions with explicit typed handlers. -/
def explicitNonLexicalCoverageCount : Nat :=
  explicitlyHandledNonLexicalFunctionNames.length

/-- Explicit non-lexical semantic coverage ratio in percentage points. -/
def explicitNonLexicalCoveragePercent : Float :=
  if nonLexicalFunctionCount = 0 then 0.0
  else (Float.ofNat explicitNonLexicalCoverageCount / Float.ofNat nonLexicalFunctionCount) * 100.0

/-- Total number of GF abstract functions declared in `Abstract.lean`. -/
def totalFunctionCount : Nat := FunctionSig.allFunctions.length

/-- Explicit semantic coverage ratio in percentage points. -/
def explicitCoveragePercent : Float :=
  if totalFunctionCount = 0 then 0.0
  else (Float.ofNat explicitCoverageCount / Float.ofNat totalFunctionCount) * 100.0

/-- GF abstract function names without explicit typed handlers.
They still linearize through deterministic symbolic fallback. -/
def uncoveredFunctionNames : List String :=
  FunctionSig.allFunctionNames.filter
    (fun name => !(explicitlyHandledFunctionNames.contains name))

end Mettapedia.Languages.GF.English.Linearization
