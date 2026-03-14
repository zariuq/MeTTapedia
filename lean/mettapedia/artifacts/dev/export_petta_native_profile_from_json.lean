import Mettapedia.Languages.MeTTa.PeTTa.ArtifactBundle
import Lean.Data.Json

/-!
# Per-Program AOT Native Profile Export

Reads a JSON file describing a PeTTaSpace (rules + facts) and exports the
full PeTTa artifact bundle including the native profile.

This is the per-program AOT bridge: Rust serializes parsed rules to JSON,
Lean ingests them, derives the semantic bundle, and exports certified artifacts.

## JSON Format

```json
{
  "rules": [
    {
      "name": "R0",
      "left": { "kind": "apply", "ctor": "foo", "args": [{ "kind": "fvar", "name": "X" }] },
      "right": { "kind": "apply", "ctor": "bar", "args": [{ "kind": "fvar", "name": "X" }] },
      "premises": []
    }
  ],
  "facts": []
}
```

Pattern JSON kinds: `fvar`, `apply`, `bvar`, `lambda`, `subst`
Premise JSON kinds: `relation_query`, `freshness`, `congruence`
-/

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Artifacts
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace PeTTaJsonIngestion

partial def parsePatternJson (j : Lean.Json) : Except String Pattern := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "fvar" =>
    let name ← j.getObjValAs? String "name"
    return .fvar name
  | "bvar" =>
    let idx ← j.getObjValAs? Nat "index"
    return .bvar idx
  | "apply" =>
    let ctor ← j.getObjValAs? String "ctor"
    let argsJson ← j.getObjVal? "args" >>= Lean.Json.getArr?
    let args ← argsJson.toList.mapM parsePatternJson
    return .apply ctor args
  | "lambda" =>
    let bodyJson ← j.getObjVal? "body"
    let body ← parsePatternJson bodyJson
    return .lambda body
  | "subst" =>
    let fnJson ← j.getObjVal? "fn"
    let argJson ← j.getObjVal? "arg"
    let fn ← parsePatternJson fnJson
    let arg ← parsePatternJson argJson
    return .subst fn arg
  | other => throw s!"unknown pattern kind '{other}'"

def parsePremiseJson (j : Lean.Json) : Except String Premise := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "relation_query" =>
    let relation ← j.getObjValAs? String "relation"
    let argsJson ← j.getObjVal? "args" >>= Lean.Json.getArr?
    let args ← argsJson.toList.mapM parsePatternJson
    return .relationQuery relation args
  | "congruence" =>
    let leftJson ← j.getObjVal? "left"
    let rightJson ← j.getObjVal? "right"
    let left ← parsePatternJson leftJson
    let right ← parsePatternJson rightJson
    return .congruence left right
  | other => throw s!"unknown premise kind '{other}'"

def parseRewriteRuleJson (j : Lean.Json) : Except String RewriteRule := do
  let name ← j.getObjValAs? String "name"
  let leftJson ← j.getObjVal? "left"
  let rightJson ← j.getObjVal? "right"
  let left ← parsePatternJson leftJson
  let right ← parsePatternJson rightJson
  let premisesJson ← j.getObjVal? "premises" >>= Lean.Json.getArr?
  let premises ← premisesJson.toList.mapM parsePremiseJson
  return { name, typeContext := [], premises, left, right }

def parsePeTTaSpaceJson (j : Lean.Json) : Except String PeTTaSpace := do
  let rulesJson ← j.getObjVal? "rules" >>= Lean.Json.getArr?
  let rules ← rulesJson.toList.mapM parseRewriteRuleJson
  let facts ← match j.getObjVal? "facts" with
    | .ok factsVal =>
      match Lean.Json.getArr? factsVal with
      | .ok factsArr => factsArr.toList.mapM parsePatternJson
      | .error _ => pure []
    | .error _ => pure []
  return (⟨facts, rules⟩ : PeTTaSpace)

end PeTTaJsonIngestion

def main (args : List String) : IO UInt32 := do
  match args with
  | [inputJsonPath, outDir] =>
    IO.println s!"reading rules from {inputJsonPath}..."
    let jsonText ← IO.FS.readFile inputJsonPath
    let json ← match Lean.Json.parse jsonText with
      | .ok j => pure j
      | .error e =>
        IO.println s!"JSON parse error: {e}"
        return 1
    match PeTTaJsonIngestion.parsePeTTaSpaceJson json with
    | .error e =>
      IO.println s!"PeTTaSpace parse error: {e}"
      return 1
    | .ok space =>
      IO.println s!"parsed PeTTaSpace: {space.rules.length} rules, {space.facts.length} facts"
      let outPath : System.FilePath := outDir
      IO.println s!"exporting PeTTa artifact bundle to {outDir}..."
      let exportCode ← exportPeTTaArtifacts outPath space .boundaryAware
      if exportCode != 0 then
        IO.println s!"export failed with code {exportCode}"
        return exportCode
      IO.println "verifying exported artifacts..."
      let checkCode ← checkPeTTaArtifacts outPath space .boundaryAware
      if checkCode != 0 then
        IO.println s!"verification failed with code {checkCode}"
        return checkCode
      IO.println "[ok] per-program native profile exported and verified"
      return 0
  | _ =>
    IO.println "usage: export_petta_native_profile_from_json <rules.json> <output-dir>"
    return 1
