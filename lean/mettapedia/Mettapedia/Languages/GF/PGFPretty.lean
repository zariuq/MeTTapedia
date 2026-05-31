import Mettapedia.Languages.GF.PGFWitnessIR

/-!
# Reversible Pretty View for PGF Witnesses

Raw `ExportedTree` values are the trust boundary for GF witnesses, but
their generated Lean syntax is not meant for human reading. This module
adds a second, reversible view of the same tree. It keeps every GF
function name and child, while rendering common wrapper constructors in
a more readable vocabulary.

The pretty string is presentation only. Reversibility lives in
`FormalGF.ofExportedTree` and `FormalGF.toExportedTree`.
-/

namespace Mettapedia.Languages.GF.PGFPretty

open Mettapedia.Languages.GF.PGFWitnessIR

structure FormalGF where
  funName : String
  args : List FormalGF
  deriving Repr

namespace FormalGF

def ofExportedTree : ExportedTree → FormalGF
  | .node name args => ⟨name, args.map ofExportedTree⟩

def toExportedTree : FormalGF → ExportedTree
  | ⟨name, args⟩ => .node name (args.map toExportedTree)

private def gfCats : List String :=
  ["N", "N2", "N3", "PN", "LN", "A", "A2", "V", "V2", "V3", "VV", "VS", "VA",
   "VQ", "V2V", "V2S", "Adv", "AdV", "AdA", "AdN", "Prep", "Predet", "Det",
   "Quant", "Conj", "Subj", "Pron", "CN", "NP", "AP", "Card", "Digits",
   "Numeral", "Interj", "Ord", "IDet", "IQuant"]

/-- Render a GF WordNet lexeme id such as `power_10_N` as `power ⟨N⟩`,
    stripping the sense number and tagging the category. Non-lexeme names
    (structural function names) are returned unchanged. -/
private def cleanLex (name : String) : String :=
  match (name.splitOn "_").reverse with
  | cat :: rest =>
    if gfCats.contains cat then
      let rest2 :=
        match rest with
        | n :: more => if n.length > 0 && n.all Char.isDigit then more else rest
        | [] => rest
      let word := (String.intercalate "_" rest2.reverse).replace "_" " "
      if word.isEmpty then name else word ++ " ⟨" ++ cat ++ "⟩"
    else name
  | [] => name

private def prettyFun : String → String
  | "PhrUtt" => "phrase"
  | "NoPConj" => "no-conjunction"
  | "NoVoc" => "no-vocative"
  | "UttS" => "sentence"
  | "UttVPShort" => "verb-phrase utterance"
  | "PredVPS" => "predication"
  | "DetCN" => "noun phrase"
  | "DetQuant" => "determiner"
  | "DefArt" => "the"
  | "IndefArt" => "a"
  | "NumSg" => "singular"
  | "NumPl" => "plural"
  | "NumCard" => "cardinal number"
  | "NumNumeral" => "numeral"
  | "UseN" => "noun"
  | "UsePN" => "proper name"
  | "UseComp_estar" => "be"
  | "CompAP" => "adjective complement"
  | "PositA" => "adjective"
  | "ComplVPS2" => "verbal predicate"
  | "MkVPS2" => "tense-modal predicate"
  | "TTAnt" => "tense/aspect"
  | "TPres" => "present tense"
  | "ASimul" => "simultaneous aspect"
  | "PPos" => "positive polarity"
  | "SlashVV" => "verb with VP complement"
  | "VPSlashPrep" => "prepositional predicate"
  | "PartNP" => "partitive noun phrase"
  | "PossNP" => "possessive noun phrase"
  | "ApposCN" => "appositive common noun"
  | other => other

/-- Node label: structural functions use the readable vocabulary; leaf
    lexemes are cleaned to `word ⟨CAT⟩`. -/
private def nodeLabel (name : String) : String :=
  let p := prettyFun name
  if p == name then cleanLex name else p

mutual
  partial def renderTree (pfx : String) (isLast : Bool) (t : FormalGF) : String :=
    let conn := if isLast then "└─ " else "├─ "
    let kidPfx := pfx ++ (if isLast then "   " else "│  ")
    match t.args with
    | [] => pfx ++ conn ++ nodeLabel t.funName ++ "\n"
    | [c] =>
      if c.args.isEmpty then
        pfx ++ conn ++ prettyFun t.funName ++ ": " ++ nodeLabel c.funName ++ "\n"
      else
        pfx ++ conn ++ prettyFun t.funName ++ "\n" ++ renderForest kidPfx [c]
    | args =>
      pfx ++ conn ++ prettyFun t.funName ++ "\n" ++ renderForest kidPfx args
  partial def renderForest (pfx : String) (ts : List FormalGF) : String :=
    match ts with
    | [] => ""
    | [x] => renderTree pfx true x
    | x :: xs => renderTree pfx false x ++ renderForest pfx xs
end

def pretty (t : FormalGF) : String :=
  match t.args with
  | [] => nodeLabel t.funName
  | [c] =>
    if c.args.isEmpty then prettyFun t.funName ++ ": " ++ nodeLabel c.funName
    else prettyFun t.funName ++ "\n" ++ renderForest "" [c]
  | args => prettyFun t.funName ++ "\n" ++ renderForest "" args

def roundTrips (t : ExportedTree) : Bool :=
  (ofExportedTree t).toExportedTree == t

def tinyExample : ExportedTree :=
  .node "PhrUtt" [
    .node "NoPConj" [],
    .node "UttS" [
      .node "PredVPS" [
        .node "UsePN" [.node "constitution_PN" []]
      ]
    ],
    .node "NoVoc" []
  ]

end FormalGF

namespace ExportedTree

def toFormalGF (t : ExportedTree) : FormalGF :=
  FormalGF.ofExportedTree t

def prettyFormalGF (t : ExportedTree) : String :=
  FormalGF.pretty (FormalGF.ofExportedTree t)

def formalGFRoundTrips (t : ExportedTree) : Bool :=
  FormalGF.roundTrips t

end ExportedTree

end Mettapedia.Languages.GF.PGFPretty
