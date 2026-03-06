import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.English.Syntax
import Mettapedia.Languages.GF.English.Pronouns
import Mettapedia.Languages.GF.English.Relatives

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

def decodeGFToken (s : String) : String :=
  String.ofList <| s.toList.map fun ch =>
    if ch = '_' || ch = '7' || ch = '8' then ' ' else ch

def dropSuffixIf (s suffix : String) : String :=
  if strEndsWith s suffix then
    strDropEnd s suffix.toList.length
  else s

def stemFrom (name suffix : String) : String :=
  decodeGFToken (dropSuffixIf name suffix)

def normalizeInterrogativeStem (s : String) : String :=
  match s with
  | "whatSg" => "what"
  | "whatPl" => "what"
  | "whoSg" => "who"
  | "whoPl" => "who"
  | other => other

def agrFromNumber (n : Number) : Agr :=
  match n with
  | .Sg => .AgP3Sg .Neutr
  | .Pl => .AgP3Pl

def mkLiteralNP (txt : String) : EnglishNP :=
  { s := fun _ => txt, agr := .AgP3Sg .Neutr }

def joinWithConj (xs : List String) (conj : String) : String :=
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

def EngValue.asN? : EngValue → Option EnglishNoun
  | EngValue.noun x => some x
  | EngValue.cn x => some x
  | _ => none

def EngValue.asCN? : EngValue → Option EnglishCN
  | EngValue.cn x => some x
  | EngValue.noun x => some x
  | _ => none

def EngValue.asA? : EngValue → Option EnglishAdj
  | EngValue.adj x => some x
  | _ => none

def EngValue.asAP? : EngValue → Option EnglishAP
  | EngValue.ap x => some x
  | _ => none

def EngValue.asDet? : EngValue → Option EnglishDet
  | EngValue.det x => some x
  | _ => none

def EngValue.asQuant? : EngValue → Option EnglishQuant
  | EngValue.quant q => some q
  | EngValue.det d => some { sSg := d.s, sPl := d.s, isDef := d.isDef }
  | _ => none

def EngValue.asNum? : EngValue → Option EnglishNumInfo
  | EngValue.num n => some n
  | _ => none

def EngValue.asCard? : EngValue → Option String
  | EngValue.card s => some s
  | EngValue.raw (.base "Card") s => some s
  | _ => none

def EngValue.asOrd? : EngValue → Option EnglishOrdInfo
  | EngValue.ord o => some o
  | _ => none

def EngValue.asNP? : EngValue → Option EnglishNP
  | EngValue.np x => some x
  | _ => none

def EngValue.asV? : EngValue → Option EnglishVerb
  | EngValue.verb x => some x
  | _ => none

def EngValue.asV2? : EngValue → Option EnglishV2
  | EngValue.verb2 x => some x
  | _ => none

def EngValue.asV3? : EngValue → Option EnglishV3Frame
  | EngValue.verb3 x => some x
  | _ => none

def EngValue.asV2Comp? : EngValue → Option EnglishV2CompFrame
  | EngValue.verb2comp x => some x
  | _ => none

def EngValue.asVP? : EngValue → Option EnglishVP
  | EngValue.vp x => some x
  | _ => none

def EngValue.asComp? : EngValue → Option EnglishComp
  | EngValue.comp x => some x
  | _ => none

def EngValue.asVPSlash? : EngValue → Option EnglishVPSlash
  | EngValue.vpslash x => some x
  | _ => none

def EngValue.asClSlash? : EngValue → Option EnglishClSlash
  | EngValue.clslash x => some x
  | _ => none

def EngValue.asQVP? : EngValue → Option EnglishQVP
  | EngValue.qvp x => some x
  | EngValue.raw (.base "QVP") s => some ⟨s⟩
  | _ => none

def EngValue.asCl? : EngValue → Option EnglishClause
  | EngValue.cls x => some x
  | _ => none

def EngValue.asQCl? : EngValue → Option EnglishClause
  | EngValue.qcl x => some x
  | _ => none

def EngValue.asRCl? : EngValue → Option EnglishRCl
  | EngValue.rcl x => some x
  | _ => none

def EngValue.asRS? : EngValue → Option EnglishRS
  | EngValue.rs x => some x
  | _ => none

def EngValue.asRP? : EngValue → Option EnglishRP
  | EngValue.rp x => some x
  | _ => none

def EngValue.asPrep? : EngValue → Option EnglishPrep
  | EngValue.prep x => some x
  | _ => none

def EngValue.asConj? : EngValue → Option EnglishConj
  | EngValue.conj x => some x
  | _ => none

def EngValue.asSubj? : EngValue → Option EnglishSubj
  | EngValue.subj x => some x
  | _ => none

def EngValue.asAdv? : EngValue → Option String
  | EngValue.adv x => some x
  | EngValue.raw (.base "Adv") x => some x
  | EngValue.raw (.base "AdV") x => some x
  | EngValue.raw (.base "IAdv") x => some x
  | _ => none

def EngValue.asPConj? : EngValue → Option String
  | EngValue.raw (.base "PConj") x => some x
  | _ => none

def EngValue.asVoc? : EngValue → Option String
  | EngValue.raw (.base "Voc") x => some x
  | _ => none

def EngValue.asTemp? : EngValue → Option EnglishTemp
  | EngValue.temp x => some x
  | EngValue.tense x => some ⟨x, .Simul⟩
  | _ => none

def EngValue.asPol? : EngValue → Option CPolarity
  | EngValue.pol x => some x
  | _ => none

def EngValue.asListNP? : EngValue → Option (List EnglishNP)
  | EngValue.listNP xs => some xs
  | EngValue.np x => some [x]
  | _ => none

def EngValue.asListCN? : EngValue → Option (List EnglishCN)
  | EngValue.listCN xs => some xs
  | EngValue.cn x => some [x]
  | EngValue.noun x => some [x]
  | _ => none

def EngValue.asListAP? : EngValue → Option (List EnglishAP)
  | EngValue.listAP xs => some xs
  | EngValue.ap x => some [x]
  | _ => none

def EngValue.asListRS? : EngValue → Option (List EnglishRS)
  | EngValue.listRS xs => some xs
  | EngValue.rs x => some [x]
  | _ => none

def EngValue.asListAdv? : EngValue → Option (List String)
  | EngValue.listAdv xs => some xs
  | EngValue.adv x => some [x]
  | EngValue.raw (.base "Adv") x => some [x]
  | _ => none

def EngValue.asListAdV? : EngValue → Option (List String)
  | EngValue.listAdV xs => some xs
  | EngValue.adv x => some [x]
  | EngValue.raw (.base "AdV") x => some [x]
  | _ => none

def EngValue.asListIAdv? : EngValue → Option (List String)
  | EngValue.listIAdv xs => some xs
  | EngValue.adv x => some [x]
  | EngValue.raw (.base "IAdv") x => some [x]
  | _ => none

def EngValue.asListDet? : EngValue → Option (List EnglishDet)
  | EngValue.listDet xs => some xs
  | EngValue.det d => some [d]
  | _ => none

def EngValue.asListS? : EngValue → Option (List String)
  | EngValue.listS xs => some xs
  | EngValue.raw (.base "S") s => some [s]
  | EngValue.raw (.base "QS") s => some [s]
  | EngValue.raw (.base "SC") s => some [s]
  | _ => none

def EngValue.asListVPS? : EngValue → Option (List String)
  | EngValue.listVPS xs => some xs
  | EngValue.raw (.base "VPS") s => some [s]
  | _ => none

def EngValue.asListVPI? : EngValue → Option (List String)
  | EngValue.listVPI xs => some xs
  | EngValue.raw (.base "VPI") s => some [s]
  | _ => none

def EngValue.asListVPS2? : EngValue → Option (List String)
  | EngValue.listVPS2 xs => some xs
  | EngValue.raw (.base "VPS2") s => some [s]
  | _ => none

def EngValue.asListVPI2? : EngValue → Option (List String)
  | EngValue.listVPI2 xs => some xs
  | EngValue.raw (.base "VPI2") s => some [s]
  | _ => none

def EngValue.asListComp? : EngValue → Option (List String)
  | EngValue.listComp xs => some xs
  | EngValue.comp c => some [c.render (.AgP3Sg .Neutr)]
  | EngValue.raw (.base "Comp") s => some [s]
  | _ => none

def EngValue.asListImp? : EngValue → Option (List String)
  | EngValue.listImp xs => some xs
  | EngValue.raw (.base "Imp") s => some [s]
  | _ => none

def EngValue.asListSymb? : EngValue → Option (List String)
  | EngValue.listSymb xs => some xs
  | EngValue.raw (.base "Symb") s => some [s]
  | _ => none


end Mettapedia.Languages.GF.English.Linearization
