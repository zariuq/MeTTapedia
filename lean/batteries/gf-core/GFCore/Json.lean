/-
# GFCore.Json — JSON codecs for GF wire types

Encodes/decodes RawTerm, ParseCandidate, FunDecl, GrammarSig
using Lean.Data.Json (available in Lean core, no external deps).

JSON format for RawTerm (matches GF PGF export):
  {"fun": "PredVP", "args": [...]}
  {"fun": "PredVP", "cat": "S", "args": [...]}   -- with optional cat hint

JSON format for ParseCandidate:
  {"language": "Eng", "surface": "...", "prob": 1.5, "tree": {...}}
-/

import Lean.Data.Json
import GFCore.Syntax

namespace GFCore

open Lean (Json ToJson FromJson toJson fromJson?)

-- ============================================================
-- RawTerm JSON
-- ============================================================

partial def rawTermToJson (t : RawTerm) : Json :=
  let fields : List (String × Json) := [("fun", toJson t.funName)]
  let fields := match t.catHint? with
    | some c => fields ++ [("cat", toJson c)]
    | none   => fields
  let fields := fields ++ [("args", Json.arr (t.args.map rawTermToJson))]
  Json.mkObj fields

partial def rawTermFromJson (j : Json) : Except String RawTerm := do
  let funName ← j.getObjValAs? String "fun"
  let catHint? : Option String := (j.getObjValAs? String "cat").toOption
  let argsJson ← j.getObjValAs? (Array Json) "args"
  let args ← argsJson.mapM rawTermFromJson
  pure (.app funName catHint? args)

instance : ToJson RawTerm where
  toJson := rawTermToJson

instance : FromJson RawTerm where
  fromJson? := rawTermFromJson

-- ============================================================
-- ParseCandidate JSON
-- ============================================================

instance : ToJson ParseCandidate where
  toJson pc :=
    let fields : List (String × Json) := [
      ("language", toJson pc.language),
      ("surface", toJson pc.surface),
      ("tree", toJson pc.tree)
    ]
    let fields := match pc.prob? with
      | some p => ("prob", toJson p) :: fields
      | none   => fields
    Json.mkObj fields

instance : FromJson ParseCandidate where
  fromJson? j := do
    let language ← j.getObjValAs? String "language"
    let surface ← j.getObjValAs? String "surface"
    let prob? : Option Float := (j.getObjValAs? Float "prob").toOption
    let tree ← j.getObjValAs? RawTerm "tree"
    pure { language, surface, prob?, tree }

-- ============================================================
-- FunDecl JSON
-- ============================================================

instance : ToJson FunStatus where
  toJson
    | .primitive   => "primitive"
    | .constructor => "constructor"
    | .defined     => "defined"

instance : FromJson FunStatus where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "primitive"   => pure .primitive
    | "constructor" => pure .constructor
    | "defined"     => pure .defined
    | other         => throw s!"unknown FunStatus: {other}"

instance : ToJson FunDecl where
  toJson d := Json.mkObj [
    ("name", toJson d.name),
    ("argCats", toJson d.argCats),
    ("resultCat", toJson d.resultCat),
    ("status", toJson d.status)
  ]

instance : FromJson FunDecl where
  fromJson? j := do
    let name ← j.getObjValAs? String "name"
    let argCats ← j.getObjValAs? (Array String) "argCats"
    let resultCat ← j.getObjValAs? String "resultCat"
    -- PGF JSON does not include FunStatus (the fun/data/def distinction is
    -- erased during PGF compilation). Default to .primitive is correct.
    let status ← match j.getObjValAs? FunStatus "status" with
      | .ok s    => pure s
      | .error _ => pure .primitive
    pure { name, argCats, resultCat, status }

-- ============================================================
-- GrammarSig JSON
-- ============================================================

instance : ToJson GrammarSig where
  toJson sig := Json.mkObj [
    ("grammar", toJson sig.grammar),
    ("startCats", toJson sig.startCats),
    ("funs", Json.mkObj (sig.funs.fold (init := []) fun acc k v =>
      (k, toJson v) :: acc)),
    ("sourceHash", toJson sig.sourceHash)
  ]

instance : FromJson GrammarSig where
  fromJson? j := do
    let grammar ← j.getObjValAs? String "grammar"
    let startCats ← j.getObjValAs? (Array String) "startCats"
    let sourceHash ← match j.getObjValAs? String "sourceHash" with
      | .ok s    => pure s
      | .error _ => pure ""
    let funsJson ← j.getObjVal? "funs"
    let funsList ← match funsJson with
      | .obj kvs =>
          let mut acc : List (String × FunDecl) := []
          for (k, v) in kvs.toList do
            let decl ← fromJson? v
            acc := (k, decl) :: acc
          pure acc
      | _ => throw "funs must be a JSON object"
    let funs := Std.HashMap.ofList funsList
    pure { grammar, startCats, funs, sourceHash }

-- ============================================================
-- IO helpers
-- ============================================================

/-- Read a JSON file and decode as an array of ParseCandidates. -/
def ParseCandidate.readFromFile (path : System.FilePath) : IO (Array ParseCandidate) := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  IO.ofExcept (fromJson? json)

/-- Read a JSON file containing a single RawTerm or array of RawTerms. -/
def RawTerm.readFromFile (path : System.FilePath) : IO (Array RawTerm) := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  match fromJson? (α := Array RawTerm) json with
  | .ok trees => pure trees
  | .error _ =>
    match fromJson? (α := RawTerm) json with
    | .ok tree => pure #[tree]
    | .error e => throw (IO.userError e)

/-- Write RawTerms to a JSON file. -/
def RawTerm.writeToFile (trees : Array RawTerm) (path : System.FilePath) : IO Unit := do
  let json := toJson trees
  IO.FS.writeFile path json.pretty

/-- Read a GrammarSig from a JSON file. -/
def GrammarSig.readFromFile (path : System.FilePath) : IO GrammarSig := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  IO.ofExcept (fromJson? json)

-- ============================================================
-- Source / FailureClass / Analysis JSON
-- ============================================================

instance : ToJson Source where
  toJson
    | .direct => Json.mkObj [("kind", "direct")]
    | .paraphrased orig conf => Json.mkObj [
        ("kind", "paraphrased"), ("original", toJson orig), ("confidence", toJson conf)]

instance : FromJson Source where
  fromJson? j := do
    let kind ← j.getObjValAs? String "kind"
    match kind with
    | "direct" => pure .direct
    | "paraphrased" => do
      let orig ← j.getObjValAs? String "original"
      let conf ← j.getObjValAs? Float "confidence"
      pure (.paraphrased orig conf)
    | other => throw s!"unknown Source kind: {other}"

instance : ToJson FailureClass where
  toJson
    | .unknownLexeme t => Json.mkObj [("kind", "unknownLexeme"), ("token", toJson t)]
    | .wrongFrame t d => Json.mkObj [("kind", "wrongFrame"), ("token", toJson t), ("detail", toJson d)]
    | .missingConstruction d => Json.mkObj [("kind", "missingConstruction"), ("description", toJson d)]
    | .noise d => Json.mkObj [("kind", "noise"), ("description", toJson d)]

instance : FromJson FailureClass where
  fromJson? j := do
    let kind ← j.getObjValAs? String "kind"
    match kind with
    | "unknownLexeme" => .unknownLexeme <$> j.getObjValAs? String "token"
    | "wrongFrame" => FailureClass.wrongFrame <$> j.getObjValAs? String "token" <*> j.getObjValAs? String "detail"
    | "missingConstruction" => .missingConstruction <$> j.getObjValAs? String "description"
    | "noise" => .noise <$> j.getObjValAs? String "description"
    | other => throw s!"unknown FailureClass kind: {other}"

instance : ToJson Analysis where
  toJson
    | .exact _expr source => Json.mkObj [
        ("status", "exact"), ("source", toJson source)]
        -- Note: CheckedExpr not serialized (it's reconstructed from RawTerm + sig)
    | .opaque surface reason => Json.mkObj [
        ("status", "opaque"), ("surface", toJson surface), ("reason", toJson reason)]

instance : FromJson Analysis where
  fromJson? j := do
    let status ← j.getObjValAs? String "status"
    match status with
    | "opaque" => do
      let surface ← j.getObjValAs? String "surface"
      let reason ← j.getObjValAs? FailureClass "reason"
      pure (.opaque surface reason)
    | _ => throw "Analysis.exact cannot be deserialized (needs GrammarSig + RawTerm)"

end GFCore
