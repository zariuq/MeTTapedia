import Mettapedia.Languages.GF.English.Linearization.Types

namespace Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Core Abstract
open English
open Syntax Pronouns Relatives
open Nouns Verbs Adjectives
structure RenderParams where
  case : Case := .Nom
  number : Number := .Sg
  tense : Tense := .Pres
  ant : Anteriority := .Simul
  pol : CPolarity := .CPos
  order : Order := .ODir true
  deriving DecidableEq, Repr, Inhabited

def renderValue (v : EngValue) (p : RenderParams) : String :=
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

def fallbackAppString (name : String) (args : List EngValue) : String :=
  let rendered := args.map (fun v => renderValue v {})
  name ++ "(" ++ String.intercalate ", " rendered ++ ")"

end Mettapedia.Languages.GF.English.Linearization
