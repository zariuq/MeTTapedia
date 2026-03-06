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
import Mettapedia.Languages.GF.English.Linearization.Types
import Mettapedia.Languages.GF.English.Linearization.Compose
import Mettapedia.Languages.GF.English.Linearization.Render

namespace Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF
open Core Abstract
open English
open Syntax Pronouns Relatives
open Nouns Verbs Adjectives
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

def evalLeafValue (env : EnglishLinEnv) (name : String) (cat : Category) : EngValue :=
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

inductive DispatchTag where
  | useN
  | detCN
  | slashV2a
  | complSlash
  | passV2
  | predVP
  deriving DecidableEq, Repr, Inhabited

/-- Small tagged front-end for proof-facing constructor reduction.
This starts the migration away from the monolithic string dispatcher without
changing external behavior. -/
def dispatchTag? : String → Option DispatchTag
  | "UseN" => some .useN
  | "DetCN" => some .detCN
  | "SlashV2a" => some .slashV2a
  | "ComplSlash" => some .complSlash
  | "PassV2" => some .passV2
  | "PredVP" => some .predVP
  | _ => none

/-- Tagged semantics for the witness-critical constructor fragment. -/
def dispatchApplyTagged (tag : DispatchTag) (args : List EngValue) : Option EngValue :=
  match tag, args with
  | .useN, [x] => x.asN? |>.map (fun n => .cn (linUseN n))
  | .detCN, [d, cn] =>
    match d.asDet?, cn.asCN? with
    | some det, some noun => some (.np (linDetCN det noun))
    | _, _ => none
  | .slashV2a, [v2] => v2.asV2? |>.map (fun x => .vpslash (slashV2a x))
  | .complSlash, [vps, np] =>
    match vps.asVPSlash?, np.asNP? with
    | some x, some y => some (.vp (fillSlashPreservingBase x y))
    | _, _ => none
  | .passV2, [v2] => v2.asV2? |>.map (fun x => .vp (passiveVP x))
  | .predVP, [np, vp] =>
    match np.asNP?, vp.asVP? with
    | some s, some v => some (.cls (linPredVP s v))
    | _, _ => none
  | _, _ => none

private def dispatchApplyLegacy (f : FunctionSig) (args : List EngValue) : Option EngValue :=
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

/-- Public dispatch entrypoint.

The tagged path gives proof-facing reductions a small, stable surface for the
most-used witness constructors, while the legacy matcher preserves the full
current behavior for everything else. -/
def dispatchApply (f : FunctionSig) (args : List EngValue) : Option EngValue :=
  match dispatchTag? f.name with
  | some tag =>
    match dispatchApplyTagged tag args with
    | some v => some v
    | none => dispatchApplyLegacy f args
  | none => dispatchApplyLegacy f args

/-! ## Proof-Facing Reduction Lemmas -/

theorem evalLeafValue_cat_N :
    evalLeafValue {} "cat_N" (.base "N") = .noun cat_N := by
  change
    (match ({} : EnglishLinEnv).lookupN "cat_N" <|>
        ({} : EnglishLinEnv).lookupCN "cat_N" <|> nounByName? "cat_N" with
      | some n => EngValue.noun n
      | none => EngValue.noun (regN (stemFrom "cat_N" "_N"))) = EngValue.noun cat_N
  have hstem : stemFrom "cat_N" "_N" = "cat" := by decide
  simp [nounByName?, cat_N, hstem]

theorem evalLeafValue_dog_N :
    evalLeafValue {} "dog_N" (.base "N") = .noun dog_N := by
  change
    (match ({} : EnglishLinEnv).lookupN "dog_N" <|>
        ({} : EnglishLinEnv).lookupCN "dog_N" <|> nounByName? "dog_N" with
      | some n => EngValue.noun n
      | none => EngValue.noun (regN (stemFrom "dog_N" "_N"))) = EngValue.noun dog_N
  have hstem : stemFrom "dog_N" "_N" = "dog" := by decide
  simp [nounByName?, dog_N, hstem]

theorem evalLeafValue_the_Det :
    evalLeafValue {} "the_Det" (.base "Det") = .det theDefArt := by
  change
    (match ({} : EnglishLinEnv).lookupDet "the_Det" <|> detByName? "the_Det" with
      | some d => EngValue.det d
      | none => EngValue.det { s := stemFrom "the_Det" "_Det", n := .Sg, isDef := false }) =
        EngValue.det theDefArt
  simp [detByName?]

theorem evalLeafValue_love_V2 :
    evalLeafValue {} "love_V2" (.base "V2") = .verb2 love_V2 := by
  change
    (match ({} : EnglishLinEnv).lookupV2 "love_V2" <|> v2ByName? "love_V2" with
      | some v2 => EngValue.verb2 v2
      | none => EngValue.verb2 (regV2 (stemFrom "love_V2" "_V2"))) = EngValue.verb2 love_V2
  simp [v2ByName?]

theorem dispatchApply_UseN_noun (n : EnglishNoun) :
    dispatchApply
        { name := "UseN", type := .arrow (.base "N") (.base "CN") }
        [.noun n] =
      some (.cn (linUseN n)) := by
  unfold dispatchApply dispatchTag? dispatchApplyTagged
  simp [EngValue.asN?]

theorem dispatchApply_DetCN (det : EnglishDet) (noun : EnglishCN) :
    dispatchApply
        { name := "DetCN", type := .arrow (.base "Det") (.arrow (.base "CN") (.base "NP")) }
        [.det det, .cn noun] =
      some (.np (linDetCN det noun)) := by
  unfold dispatchApply dispatchTag? dispatchApplyTagged
  simp [EngValue.asDet?, EngValue.asCN?]

theorem dispatchApply_SlashV2a (v2 : EnglishV2) :
    dispatchApply
        { name := "SlashV2a", type := .arrow (.base "V2") (.base "VPSlash") }
        [.verb2 v2] =
      some (.vpslash (slashV2a v2)) := by
  unfold dispatchApply dispatchTag? dispatchApplyTagged
  simp [EngValue.asV2?]

theorem dispatchApply_ComplSlash (vps : EnglishVPSlash) (np : EnglishNP) :
    dispatchApply
        { name := "ComplSlash", type := .arrow (.base "VPSlash") (.arrow (.base "NP") (.base "VP")) }
        [.vpslash vps, .np np] =
      some (.vp (fillSlashPreservingBase vps np)) := by
  unfold dispatchApply dispatchTag? dispatchApplyTagged
  simp [EngValue.asVPSlash?, EngValue.asNP?]

theorem dispatchApply_PassV2 (v2 : EnglishV2) :
    dispatchApply
        { name := "PassV2", type := .arrow (.base "V2") (.base "VP") }
        [.verb2 v2] =
      some (.vp (passiveVP v2)) := by
  unfold dispatchApply dispatchTag? dispatchApplyTagged
  simp [EngValue.asV2?]

theorem dispatchApply_PredVP (np : EnglishNP) (vp : EnglishVP) :
    dispatchApply
        { name := "PredVP", type := .arrow (.base "NP") (.arrow (.base "VP") (.base "Cl")) }
        [.np np, .vp vp] =
      some (.cls (linPredVP np vp)) := by
  unfold dispatchApply dispatchTag? dispatchApplyTagged
  simp [EngValue.asNP?, EngValue.asVP?]

mutual

def evalNode (env : EnglishLinEnv) : AbstractNode → EngValue
  | .leaf name cat => evalLeafValue env name cat
  | .apply f args =>
    let argVals := evalArgs env args
    match dispatchApply f argVals with
    | some v => v
    | none =>
      if argVals.isEmpty then
        evalLeafValue env f.name (FunctionSig.resultCategory f.type)
      else
        .raw (FunctionSig.resultCategory f.type) (fallbackAppString f.name argVals)
termination_by
  n => sizeOf n

def evalArgs (env : EnglishLinEnv) : List AbstractNode → List EngValue
  | [] => []
  | a :: as => evalNode env a :: evalArgs env as
termination_by
  xs => sizeOf xs

decreasing_by
  ·
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.lt_succ_of_le (Nat.le_add_right (sizeOf a) (sizeOf as)))
  ·
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.lt_succ_of_le (Nat.le_add_left (sizeOf as) (sizeOf a)))

end

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

end Mettapedia.Languages.GF.English.Linearization
