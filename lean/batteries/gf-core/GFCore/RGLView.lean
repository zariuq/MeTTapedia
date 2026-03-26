/-
# GFCore.RGLView — Peel RGL wrappers, expose semantic core

Transforms a CheckedExpr (full RGL tree with tense/pol/phrase wrappers)
into a readable semantic view.

Input:  PhrUtt NoPConj (UttS (PredVPS (DetCN (DetQuant IndefArt NumSg)
          (UseN star_2_N)) (ComplVPS2 (MkVPS2 (TTAnt TPres ASimul) PPos
          (SlashV2a produce_6_V2)) (MassNP (UseN light_1_N))))) NoVoc

Output: RGLView.pred "produce_6_V2"
          (RGLView.det .indefinite .singular (RGLView.noun "star_2_N"))
          (RGLView.mass (RGLView.noun "light_1_N"))

This is Layer 3 of the architecture: reusable across RGL-based grammars.
Only handles ~30 structural constructors; lexical leaves pass through as names.
-/

import GFCore.Syntax

namespace GFCore

/-- Determiner type extracted from RGL. -/
inductive DetKind where
  | definite
  | indefinite
  | mass        -- no determiner (mass noun)
  | possessive (owner : String)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Number extracted from RGL. -/
inductive NumKind where
  | singular
  | plural
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Polarity extracted from RGL. -/
inductive Polarity where
  | positive
  | negative
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Tense extracted from RGL. -/
inductive Tense where
  | present
  | past
  | future
  | conditional
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Which copular surface constructor produced this view.
    Preserved so NormClause can decide argument order. -/
inductive CopulaOrigin where
  | predVPUseComp
  | predVPSMkVPS
  | focusComp
  | advIsNP
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Semantic view of an RGL parse tree — readable, structural.
    Lexical items are represented by their GF function name (e.g., "star_2_N").
    Structural wrappers are peeled away. -/
inductive RGLView where
  | noun    (name : String)
  | adj     (name : String)
  | verb    (name : String)
  | prep    (name : String)
  | adv     (name : String)
  | det     (kind : DetKind) (num : NumKind) (cn : RGLView)
  | mass    (cn : RGLView)
  | adjMod  (adj : RGLView) (cn : RGLView)
  | advMod  (adv : RGLView) (vp : RGLView)
  | prepNP  (prep : RGLView) (np : RGLView)
  | pred    (subject : RGLView) (verbPhrase : RGLView)
  | copularSurface (origin : CopulaOrigin) (lhs : RGLView) (rhs : RGLView)
  | transV  (verb : RGLView) (object : RGLView)
  | passiveV (verb : RGLView)
  | reflV   (verb : RGLView) (reflArg : RGLView)
  | sentence (tense : Tense) (pol : Polarity) (core : RGLView)
  | properNoun (name : String)
  | pronoun (name : String)
  | coordAnd (xs : List RGLView)
  | coordOr  (xs : List RGLView)
  | kindOf  (kind : RGLView) (of_ : RGLView)  -- "X is a kind of Y"
  | opaque  (funName : String) (args : List RGLView)  -- fallback for unhandled constructors
  deriving Repr, Inhabited

/-- Extract a semantic view from a CheckedExpr by pattern-matching
    on known RGL constructor names. Unknown constructors become `opaque`. -/
partial def toRGLView (e : CheckedExpr) : RGLView :=
  let name := e.funName
  let args := e.args
  match name with
  -- Outer wrappers: peel away
  | "PhrUtt" =>
    -- PhrUtt pconj utt voc → just the utt
    if args.size ≥ 2 then toRGLView args[1]!
    else .opaque name (args.toList.map toRGLView)
  | "UttS" | "UttNP" | "UttAdv" =>
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  -- Tense/polarity wrappers
  | "UseCl" =>
    -- UseCl temp pol cl
    if args.size ≥ 3 then
      let tense := extractTense args[0]!
      let pol := extractPolarity args[1]!
      let core := toRGLView args[2]!
      .sentence tense pol core
    else .opaque name (args.toList.map toRGLView)
  -- Predication (ParseEng style)
  | "PredVPS" =>
    -- PredVPS np vps
    if args.size ≥ 2 then
      .pred (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  | "PredVP" =>
    -- PredVP np vp
    if args.size ≥ 2 then
      .pred (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  -- VPS constructors (Parse-specific)
  | "MkVPS" =>
    -- MkVPS temp pol vp → sentence wrapper + vp
    if args.size ≥ 3 then
      let tense := extractTense args[0]!
      let pol := extractPolarity args[1]!
      let core := toRGLView args[2]!
      .sentence tense pol core
    else .opaque name (args.toList.map toRGLView)
  | "MkVPS2" =>
    -- MkVPS2 temp pol slash → peel tense/pol, pass slash through
    if args.size ≥ 3 then
      let core := toRGLView args[2]!
      core  -- tense/pol handled at sentence level
    else .opaque name (args.toList.map toRGLView)
  | "ComplVPS2" =>
    -- ComplVPS2 vps2 np → transitive verb + object
    if args.size ≥ 2 then
      .transV (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  | "ReflVPS2" =>
    -- ReflVPS2 vps2 reflArg
    if args.size ≥ 2 then
      .reflV (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  -- VP constructors
  | "ComplSlash" =>
    if args.size ≥ 2 then
      .transV (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  | "SlashV2a" =>
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  | "UseV" =>
    if args.size ≥ 1 then .verb args[0]!.funName
    else .opaque name []
  | "UseComp" | "UseComp_estar" | "UseComp_ser" =>
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  | "CompNP" | "CompCN" =>
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  | "CompAP" =>
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  | "CompAdv" =>
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  | "AdvVP" | "AdvVPS" =>
    if args.size ≥ 2 then
      .advMod (toRGLView args[1]!) (toRGLView args[0]!)
    else .opaque name (args.toList.map toRGLView)
  | "VPSlashPrep" =>
    if args.size ≥ 2 then
      .opaque "VPSlashPrep" [toRGLView args[0]!, toRGLView args[1]!]
    else .opaque name (args.toList.map toRGLView)
  | "PassV2" | "PassVPSlash" =>
    if args.size ≥ 1 then .passiveV (toRGLView args[0]!)
    else .opaque name []
  -- NP constructors
  | "DetCN" =>
    if args.size ≥ 2 then
      let (detKind, numKind) := extractDet args[0]!
      .det detKind numKind (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  | "MassNP" =>
    if args.size ≥ 1 then .mass (toRGLView args[0]!)
    else .opaque name []
  | "UsePN" =>
    if args.size ≥ 1 then .properNoun args[0]!.funName
    else .opaque name []
  | "UsePron" =>
    if args.size ≥ 1 then .pronoun args[0]!.funName
    else .opaque name []
  | "AdjAsNP" =>
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  | "PrepNP" =>
    if args.size ≥ 2 then
      .prepNP (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  -- CN constructors
  | "UseN" =>
    if args.size ≥ 1 then .noun args[0]!.funName
    else .opaque name []
  | "AdjCN" =>
    if args.size ≥ 2 then
      .adjMod (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  | "AdvCN" =>
    if args.size ≥ 2 then
      .advMod (toRGLView args[1]!) (toRGLView args[0]!)
    else .opaque name (args.toList.map toRGLView)
  | "ComplN2" =>
    -- ComplN2 n2 np → kindOf pattern (often "kind of X")
    if args.size ≥ 2 then
      .kindOf (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  -- AP constructors
  | "PositA" =>
    if args.size ≥ 1 then .adj args[0]!.funName
    else .opaque name []
  -- Focused constructions: FocusComp(complement, matrix)
  -- Preserves origin so NormClause can swap arguments correctly
  | "FocusComp" =>
    if args.size ≥ 2 then
      .copularSurface .focusComp (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  -- Determiners (pass through — extracted by DetCN handler)
  | "DetQuant" | "DetQuantOrd" =>
    .opaque name (args.toList.map toRGLView)
  -- Coordination
  | "ConjS" | "ConjNP" | "ConjAP" | "ConjAdv" =>
    if args.size ≥ 2 then
      let conjName := args[0]!.funName
      let items := extractConjList args[1]!
      if conjName == "and_Conj" then .coordAnd items
      else .coordOr items
    else .opaque name (args.toList.map toRGLView)
  -- Additional CN constructors
  | "ApposCN" =>
    -- ApposCN cn np → cn modified by np (apposition)
    if args.size ≥ 2 then .adjMod (toRGLView args[1]!) (toRGLView args[0]!)
    else .opaque name (args.toList.map toRGLView)
  | "PartNP" =>
    -- PartNP cn np → "cn of np" (partitive)
    if args.size ≥ 2 then .kindOf (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  | "PossNP" =>
    -- PossNP cn np → "np's cn"
    if args.size ≥ 2 then .adjMod (toRGLView args[1]!) (toRGLView args[0]!)
    else .opaque name (args.toList.map toRGLView)
  -- Additional AP constructors
  | "CompoundAP" =>
    -- CompoundAP n a → compound adjective from noun+adj
    if args.size ≥ 2 then .adjMod (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  | "OrdSuperl" =>
    -- OrdSuperl a → superlative
    if args.size ≥ 1 then .adj (args[0]!.funName ++ "_superl")
    else .opaque name []
  -- Additional VP constructors
  | "AdvVPSlash" =>
    -- AdvVPSlash vpslash adv
    if args.size ≥ 2 then .advMod (toRGLView args[1]!) (toRGLView args[0]!)
    else .opaque name (args.toList.map toRGLView)
  | "Slash2V3" =>
    -- Slash2V3 v3 np → verb with indirect object
    if args.size ≥ 2 then .transV (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  -- Additional NP constructors
  | "UseDAP" | "DetDAP" =>
    -- Pass through to child
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  | "ReflPoss" =>
    -- ReflPoss num cn → "its own cn"
    if args.size ≥ 2 then .det (.possessive "self") .singular (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  -- GenModNP: genitive "the earth's rotation"
  | "GenModNP" =>
    if args.size ≥ 3 then
      -- GenModNP num np cn → possessive
      .det (.possessive (args[1]!.funName)) .singular (toRGLView args[2]!)
    else if args.size ≥ 2 then
      .adjMod (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  -- DetCNN: CN conjunction "day and night"
  | "DetCNN" =>
    if args.size ≥ 3 then
      -- DetCNN det conj cnn → coordinated NP
      let conjName := args[1]!.funName
      if conjName == "and_Conj" then
        .coordAnd [toRGLView args[0]!, toRGLView args[2]!]
      else
        .coordOr [toRGLView args[0]!, toRGLView args[2]!]
    else .opaque name (args.toList.map toRGLView)
  -- SentCN: sentence-modified CN "energy that is produced"
  | "SentCN" =>
    if args.size ≥ 2 then
      -- SentCN cn sc → just pass through the CN (simplified)
      toRGLView args[0]!
    else .opaque name []
  -- EmbedPresPart: present participle embedding
  | "EmbedPresPart" =>
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  -- RelCN: relative clause modification
  | "RelCN" =>
    if args.size ≥ 2 then
      -- RelCN cn rs → just pass through the CN (simplified)
      toRGLView args[0]!
    else .opaque name []
  -- UseRCl, EmptyRelSlash: relative clause internals
  | "UseRCl" =>
    if args.size ≥ 3 then toRGLView args[2]!
    else .opaque name (args.toList.map toRGLView)
  | "EmptyRelSlash" =>
    if args.size ≥ 1 then toRGLView args[0]!
    else .opaque name []
  -- SlashPrep: V + Prep
  | "SlashPrep" =>
    if args.size ≥ 2 then toRGLView args[0]!
    else .opaque name (args.toList.map toRGLView)
  -- AdvIsNP: existential/locative ("here is the tree")
  | "AdvIsNP" =>
    if args.size ≥ 2 then
      .copularSurface .advIsNP (toRGLView args[0]!) (toRGLView args[1]!)
    else .opaque name (args.toList.map toRGLView)
  -- Noise wrappers to skip
  | "NoPConj" | "NoVoc" | "TTAnt" | "TPres" | "TPast" | "TFut" | "TCond"
  | "ASimul" | "AAnter" | "PPos" | "PNeg"
  | "IndefArt" | "DefArt" | "NumSg" | "NumPl" =>
    .opaque name []
  -- Lexical leaves: use decl.resultCat from CheckedExpr (not name suffixes)
  | _ =>
    if args.isEmpty then
      let cat := e.decl.resultCat
      if cat == "N" || cat == "N2" || cat == "N3" then .noun name
      else if cat == "A" || cat == "A2" then .adj name
      else if cat == "V" || cat == "V2" || cat == "V3"
           || cat == "VS" || cat == "VV" || cat == "VA"
           || cat == "V2V" || cat == "V2S" then .verb name
      else if cat == "Prep" then .prep name
      else if cat == "Adv" then .adv name
      else if cat == "PN" then .properNoun name
      else if cat == "Pron" then .pronoun name
      else .opaque name []
    else
      .opaque name (args.toList.map toRGLView)
where
  extractTense (e : CheckedExpr) : Tense :=
    -- TTAnt tense ant → extract tense
    if e.funName == "TTAnt" && e.args.size ≥ 1 then
      match e.args[0]!.funName with
      | "TPres" => .present
      | "TPast" => .past
      | "TFut"  => .future
      | "TCond" => .conditional
      | _ => .present
    else .present

  extractPolarity (e : CheckedExpr) : Polarity :=
    match e.funName with
    | "PPos" => .positive
    | "PNeg" => .negative
    | _ => .positive

  extractDet (e : CheckedExpr) : DetKind × NumKind :=
    -- DetQuant quant num
    if e.funName == "DetQuant" && e.args.size ≥ 2 then
      let kind := match e.args[0]!.funName with
        | "IndefArt" => .indefinite
        | "DefArt" => .definite
        | _ => .indefinite  -- TODO: handle PossNP etc.
      let num := match e.args[1]!.funName with
        | "NumSg" => .singular
        | "NumPl" => .plural
        | _ => .singular
      (kind, num)
    else (.indefinite, .singular)

  extractConjList (e : CheckedExpr) : List RGLView :=
    match e.funName with
    | "BaseS" | "BaseNP" | "BaseAP" | "BaseAdv" =>
      e.args.toList.map toRGLView
    | "ConsS" | "ConsNP" | "ConsAP" | "ConsAdv" =>
      if e.args.size ≥ 2 then
        toRGLView e.args[0]! :: extractConjList e.args[1]!
      else e.args.toList.map toRGLView
    | _ => [toRGLView e]

/-- Pretty-print an RGLView for human reading. -/
partial def RGLView.pretty : RGLView → String
  | .noun n => n
  | .adj a => a
  | .verb v => v
  | .prep p => p
  | .adv a => a
  | .properNoun n => n
  | .pronoun p => p
  | .det k num cn =>
    let d := match k with | .definite => "the" | .indefinite => "a" | .mass => "" | .possessive o => s!"{o}'s"
    let n := match num with | .singular => "" | .plural => "(pl)"
    s!"{d}{n} {cn.pretty}"
  | .mass cn => cn.pretty
  | .adjMod a c => s!"{a.pretty} {c.pretty}"
  | .advMod av vp => s!"{vp.pretty} {av.pretty}"
  | .prepNP pr np => s!"{pr.pretty} {np.pretty}"
  | .pred subj vp => s!"{subj.pretty} | {vp.pretty}"
  | .copularSurface origin lhs rhs =>
    let o := match origin with | .focusComp => "[focus]" | .advIsNP => "[exist]" | _ => ""
    s!"{o}{lhs.pretty} is {rhs.pretty}"
  | .transV v o => s!"{v.pretty}({o.pretty})"
  | .passiveV v => s!"passive({v.pretty})"
  | .reflV v arg => s!"{v.pretty}(refl: {arg.pretty})"
  | .sentence t p core =>
    let ts := match t with | .present => "" | .past => "[past]" | .future => "[fut]" | .conditional => "[cond]"
    let ps := match p with | .positive => "" | .negative => "[neg]"
    s!"{ts}{ps}{core.pretty}"
  | .coordAnd xs => String.intercalate " AND " (xs.map RGLView.pretty)
  | .coordOr xs => String.intercalate " OR " (xs.map RGLView.pretty)
  | .kindOf kind of_ => s!"{kind.pretty} of {of_.pretty}"
  | .opaque f args =>
    if args.isEmpty then s!"[{f}]"
    else s!"[{f}]({String.intercalate ", " (args.map RGLView.pretty)})"

end GFCore
