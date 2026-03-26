/-
# GFCore.LexGen — Generate GF lexicon modules from data

Reads lexicon rows (JSONL) and generates:
  - Abstract GF module (fun water_N : N ;)
  - English concrete module (lin water_N = mkN "water" ;)

Adding a word = adding one JSONL row + regenerating.
No hand-editing of GF or Lean files.
-/

import Lean.Data.Json
import GFCore.Syntax

namespace GFCore

open Lean (Json ToJson FromJson toJson fromJson?)

/-- A lexicon entry. Each row becomes one GF abstract + concrete definition. -/
structure LexRow where
  abs    : String          -- e.g., "water_N"
  cat    : String          -- e.g., "N", "V", "V2", "A", "PN", "Prep", "Adv"
  lemma  : String          -- e.g., "water"
  comp?  : Option String   -- comparative (A only)
  super? : Option String   -- superlative (A only)
  past?  : Option String   -- past tense (V/V2 only)
  pp?    : Option String   -- past participle (V/V2 only)
  status : String := "proposed"  -- "proposed" | "verified"
  source : String := "mined"     -- "mined" | "manual" | "llm"
  deriving Repr, Inhabited

instance : ToJson LexRow where
  toJson r := Json.mkObj (
    [("abs", toJson r.abs), ("cat", toJson r.cat), ("lemma", toJson r.lemma),
     ("status", toJson r.status), ("source", toJson r.source)]
    ++ (match r.comp? with | some c => [("comp", toJson c)] | none => [])
    ++ (match r.super? with | some s => [("super", toJson s)] | none => [])
    ++ (match r.past? with | some p => [("past", toJson p)] | none => [])
    ++ (match r.pp? with | some p => [("pp", toJson p)] | none => []))

instance : FromJson LexRow where
  fromJson? j := do
    let abs ← j.getObjValAs? String "abs"
    let cat ← j.getObjValAs? String "cat"
    let lemma ← j.getObjValAs? String "lemma"
    let status := (j.getObjValAs? String "status").toOption.getD "proposed"
    let source := (j.getObjValAs? String "source").toOption.getD "mined"
    let comp? := (j.getObjValAs? String "comp").toOption
    let super? := (j.getObjValAs? String "super").toOption
    let past? := (j.getObjValAs? String "past").toOption
    let pp? := (j.getObjValAs? String "pp").toOption
    pure { abs, cat, lemma, comp?, super?, past?, pp?, status, source }

/-- Read a JSONL lexicon file (one JSON object per line). -/
def readLexicon (path : System.FilePath) : IO (Array LexRow) := do
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n" |>.filter (· != "")
  let mut rows : Array LexRow := #[]
  for line in lines do
    match Json.parse line >>= fromJson? (α := LexRow) with
    | .ok row => rows := rows.push row
    | .error e => IO.eprintln s!"warning: skipping bad lexicon line: {e}"
  pure rows

/-- Generate abstract GF module from lexicon rows.
    Output: `abstract LexAbs = Grammar ** { fun word_N : N ; ... }` -/
def generateAbstractGF (modName : String) (rows : Array LexRow) : String := Id.run do
  let mut out := s!"abstract {modName} = Grammar ** " ++ "{\n  fun\n"
  for row in rows do
    out := out ++ s!"    {row.abs} : {row.cat} ;\n"
  out := out ++ "}\n"
  return out

/-- Supported GF lexical categories for code generation. -/
def supportedCategories : Array String :=
  #["N", "PN", "Prep", "Adv", "A", "V", "V2", "V3", "VS", "VV", "VA", "N2", "N3", "A2"]

/-- Generate the `mkX` call for a lexicon row in GF's ParadigmsEng.
    Returns an error for unsupported categories — never silently defaults. -/
def mkCall (row : LexRow) : Except String String :=
  let q s := "\"" ++ s ++ "\""
  match row.cat with
  | "N" => .ok s!"mkN {q row.lemma}"
  | "PN" => .ok s!"mkPN {q row.lemma}"
  | "Prep" => .ok s!"mkPrep {q row.lemma}"
  | "Adv" => .ok s!"mkAdv {q row.lemma}"
  | "A" =>
    match row.comp?, row.super? with
    | some c, some s => .ok s!"mkA {q row.lemma} {q c} {q s} {q row.lemma}"
    | _, _ => .ok s!"mkA {q row.lemma}"
  | "V" =>
    match row.past?, row.pp? with
    | some p, some pp => .ok s!"mkV {q row.lemma} {q p} {q pp}"
    | _, _ => .ok s!"mkV {q row.lemma}"
  | "V2" =>
    match row.past?, row.pp? with
    | some p, some pp => .ok s!"mkV2 (mkV {q row.lemma} {q p} {q pp})"
    | _, _ => .ok s!"mkV2 (mkV {q row.lemma})"
  | "V3" => .ok s!"mkV3 (mkV {q row.lemma})"
  | "VS" => .ok s!"mkVS (mkV {q row.lemma})"
  | "VV" => .ok s!"mkVV (mkV {q row.lemma})"
  | "VA" => .ok s!"mkVA (mkV {q row.lemma})"
  | "N2" => .ok s!"mkN2 (mkN {q row.lemma})"
  | "N3" => .ok s!"mkN3 (mkN {q row.lemma})"
  | "A2" => .ok s!"mkA2 (mkA {q row.lemma})"
  | other => .error s!"unsupported GF category '{other}' for word '{row.abs}' (lemma: {row.lemma})"

/-- Generate English concrete GF module from lexicon rows.
    Returns errors for any rows with unsupported categories. -/
def generateConcreteEngGF (absName engName : String) (rows : Array LexRow)
    : Except (Array String) String := do
  let mut out := s!"concrete {engName} of {absName} = GrammarEng ** open ParadigmsEng in " ++ "{\n  lin\n"
  let mut errors : Array String := #[]
  for row in rows do
    match mkCall row with
    | .ok call => out := out ++ s!"    {row.abs} = {call} ;\n"
    | .error e => errors := errors.push e
  out := out ++ "}\n"
  if errors.isEmpty then .ok out
  else .error errors

end GFCore
