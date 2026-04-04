/-
# GFCore.SigGen — Generate GrammarSig from GF's PGF JSON export

Reads the JSON that `gf --output-format=json` produces and extracts
a GrammarSig. This replaces hand-written signature definitions.

The PGF JSON format (abstract section):
  { "abstract": {
      "name": "GrammarName",
      "startcat": "S",
      "funs": {
        "DetCN": { "args": ["Det", "CN"], "cat": "NP" },
        "UseV":  { "args": ["V"],         "cat": "VP" },
        ...
      }
    }
  }
-/

import Lean.Data.Json
import GFCore.Syntax
import GFCore.Json

namespace GFCore

open Lean (Json FromJson fromJson? ToJson toJson)

/-- Extract a GrammarSig from a GF PGF JSON export file.
    Reads the "abstract" section: name, startcat, and all function signatures. -/
def sigFromPGFJson (json : Json) (sourceHash : String := "") : Except String GrammarSig := do
  let abstract ← json.getObjVal? "abstract"
  let grammar ← abstract.getObjValAs? String "name"
  -- startcat is required — a PGF without it is corrupt or incomplete
  let startCat ← abstract.getObjValAs? String "startcat"
    |>.mapError (fun _ => "PGF JSON missing required 'startcat' field in abstract section")
  let funsObj ← abstract.getObjVal? "funs"
  let funsList ← match funsObj with
    | .obj kvs =>
      let mut acc : List (String × FunDecl) := []
      for (name, info) in kvs.toList do
        let argCats ← info.getObjValAs? (Array String) "args"
        let resultCat ← info.getObjValAs? String "cat"
        let decl : FunDecl := {
          name := name
          argCats := argCats
          resultCat := resultCat
          status := .primitive  -- PGF JSON doesn't distinguish; enrich later if needed
        }
        acc := (name, decl) :: acc
      pure acc
    | _ => throw "abstract.funs must be a JSON object"
  pure {
    grammar := grammar
    startCats := #[startCat]
    funs := Std.HashMap.ofList funsList
    sourceHash := sourceHash
  }

/-- Compute a simple hash of a string (FNV-1a 64-bit).
    Not cryptographic, but sufficient for change detection. -/
private def fnv1aHash (s : String) : String :=
  let basis : UInt64 := 14695981039346656037
  let prime : UInt64 := 1099511628211
  let h := s.foldl (init := basis) fun h c =>
    (h ^^^ c.toNat.toUInt64) * prime
  s!"{h}"

/-- Read a PGF JSON export file and produce a GrammarSig.
    Computes sourceHash from file contents for change detection. -/
def sigFromPGFJsonFile (path : System.FilePath) : IO GrammarSig := do
  let contents ← IO.FS.readFile path
  let hash := fnv1aHash contents
  let json ← IO.ofExcept (Json.parse contents)
  IO.ofExcept (sigFromPGFJson json hash)

/-- Lean identifiers can't start with digits or contain special chars. -/
private def sanitizeName (s : String) : String :=
  let s := if s.front?.map Char.isDigit |>.getD false then "f_" ++ s else s
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

private def q (s : String) : String := "\"" ++ s ++ "\""

/-- Generate a Lean source file defining a GrammarSig from a PGF JSON export.
    The generated file has no dependencies beyond GFCore. -/
def generateSigLean (sig : GrammarSig) (namespace_ : String) : String := Id.run do
  let mut out := ""
  out := out ++ s!"-- AUTO-GENERATED from GF PGF export. Do not edit.\n"
  out := out ++ s!"-- Grammar: {sig.grammar}\n"
  out := out ++ s!"-- Source hash: {sig.sourceHash}\n"
  out := out ++ s!"-- Functions: {sig.funs.size}\n\n"
  out := out ++ "import GFCore.Syntax\nimport Std.Data.HashMap\n\n"
  out := out ++ s!"namespace {namespace_}\n\nopen GFCore\n\n"
  let lbrace := "{"
  let rbrace := "}"
  -- Individual function declarations
  for (name, decl) in sig.funs.toList do
    let argCatsStr := String.intercalate ", " (decl.argCats.toList.map q)
    out := out ++ s!"private def {sanitizeName name} : FunDecl :=\n"
    out := out ++ s!"  {lbrace} name := {q name}, argCats := #[{argCatsStr}],"
    out := out ++ s!" resultCat := {q decl.resultCat}, status := .primitive {rbrace}\n\n"
  out := out ++ "/-- The list of function declarations (kernel-reducible).\n"
  out := out ++ "    Use this for proofs; `sig.funs` (HashMap) is for runtime lookup. -/\n"
  out := out ++ "def funsList : List (String × FunDecl) :=\n"
  out := out ++ "  [\n"
  for (name, _) in sig.funs.toList do
    out := out ++ s!"    ({q name}, {sanitizeName name}),\n"
  out := out ++ "  ]\n\n"
  -- The signature definition
  let startCatsStr := String.intercalate ", " (sig.startCats.toList.map q)
  out := out ++ "def sig : GrammarSig where\n"
  out := out ++ s!"  grammar := {q sig.grammar}\n"
  out := out ++ s!"  startCats := #[{startCatsStr}]\n"
  out := out ++ s!"  sourceHash := {q sig.sourceHash}\n"
  out := out ++ "  funs := Std.HashMap.ofList funsList\n\n"
  out := out ++ s!"end {namespace_}\n"
  return out

end GFCore
