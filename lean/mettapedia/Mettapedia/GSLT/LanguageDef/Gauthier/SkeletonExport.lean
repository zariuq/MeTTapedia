/-
# Lean-to-JSON export for the authenticated GSLT2GSLT skeleton

The caller supplies SHA-256 digests of this module and `Skeleton.lean`; the
freshness gate computes those digests from the repository files before invoking
this executable.  All semantic table data and positive flag rows are rendered
from proved Lean values.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.Skeleton

namespace Mettapedia.GSLT.LanguageDef.GauthierSkeletonExport

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton

private def skeletonSource : String :=
  "Mettapedia/lean/mettapedia/Mettapedia/GSLT/LanguageDef/Gauthier/Skeleton.lean"

private def exporterSource : String :=
  "Mettapedia/lean/mettapedia/Mettapedia/GSLT/LanguageDef/Gauthier/SkeletonExport.lean"

private def jsonEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c => c.toString

private def jsonString (value : String) : String :=
  "\"" ++ String.join (value.toList.map jsonEscapeChar) ++ "\""

private def jsonBool (value : Bool) : String :=
  if value then "true" else "false"

private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def roleName : ChildRole → String
  | .code => "code"
  | .value => "value"

private def theoremName? (id : Nat) : Option String :=
  (orgCertifiedCommFlags.find? (fun row => row.opId == id)).map (·.theoremName)

private def renderProvenance (id : Nat) : String :=
  let comm := match theoremName? id with
    | some name => jsonString name
    | none => "null"
  "{\"comm\":" ++ comm ++ "}"

private def renderEntry {σ : Type} (id : Nat) (tableEntry : Entry σ) : String :=
  let roles := childRoles tableEntry |>.map (jsonString ∘ roleName)
  let comm := exportedCommFlag id
  "{" ++
    "\"id\":" ++ toString id ++ "," ++
    "\"name\":" ++ jsonString tableEntry.name ++ "," ++
    "\"arity\":" ++ toString tableEntry.arity ++ "," ++
    "\"child_roles\":" ++ jsonArray roles ++ "," ++
    "\"flags\":{" ++
      "\"comm\":" ++ jsonBool comm ++ "," ++
      "\"assoc\":false," ++
      "\"identity_of\":null," ++
      "\"partial\":false," ++
      "\"stateful\":false," ++
      "\"higher_order\":" ++ jsonBool (tableEntry.hoArity > 0) ++
    "}," ++
    "\"flag_provenance\":" ++ renderProvenance id ++ "," ++
    "\"cost_grade\":1" ++
  "}"

private def renderEntries {σ : Type} : Nat → List (Entry σ) → List String
  | _, [] => []
  | id, tableEntry :: rest =>
      renderEntry id tableEntry :: renderEntries (id + 1) rest

def renderOrgTable (skeletonSha256 exporterSha256 : String) : String :=
  "{" ++
    "\"schema\":\"gslt.org.language_table.v1\"," ++
    "\"language\":\"org\"," ++
    "\"source\":" ++
      jsonString ("lean:" ++ skeletonSource ++ "@sha256:" ++ skeletonSha256) ++ "," ++
    "\"lean_sources\":[" ++
      "{\"path\":" ++ jsonString skeletonSource ++
        ",\"sha256\":" ++ jsonString skeletonSha256 ++ "}," ++
      "{\"path\":" ++ jsonString exporterSource ++
        ",\"sha256\":" ++ jsonString exporterSha256 ++ "}" ++
    "]," ++
    "\"ops\":" ++ jsonArray (renderEntries 0 orgMemoSignature) ++
  "}\n"

private def isLowerHex (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

private def validSha256 (digest : String) : Bool :=
  digest.length == 64 && digest.toList.all isLowerHex

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [skeletonSha256, exporterSha256, "check", outputPath] =>
      if !validSha256 skeletonSha256 then
        IO.eprintln "invalid Skeleton.lean SHA-256 (expected 64 lowercase hex digits)"
        pure 1
      else if !validSha256 exporterSha256 then
        IO.eprintln "invalid SkeletonExport.lean SHA-256 (expected 64 lowercase hex digits)"
        pure 1
      else
        let expected := renderOrgTable skeletonSha256 exporterSha256
        let actual ← IO.FS.readFile outputPath
        if actual == expected then
          IO.println s!"authenticated org table is fresh ({actual.toUTF8.size} bytes)"
          pure 0
        else
          IO.eprintln "authenticated org table is stale; regenerate it from SkeletonExport.lean"
          pure 1
  | [skeletonSha256, exporterSha256, outputPath] =>
      if !validSha256 skeletonSha256 then
        IO.eprintln "invalid Skeleton.lean SHA-256 (expected 64 lowercase hex digits)"
        pure 1
      else if !validSha256 exporterSha256 then
        IO.eprintln "invalid SkeletonExport.lean SHA-256 (expected 64 lowercase hex digits)"
        pure 1
      else
        let output := renderOrgTable skeletonSha256 exporterSha256
        IO.FS.writeFile outputPath output
        IO.println s!"wrote {output.toUTF8.size} bytes to {outputPath}"
        pure 0
  | _ =>
      IO.eprintln
        "usage: SkeletonExport <skeleton-sha256> <exporter-sha256> [check] <output.json>"
      pure 1

end Mettapedia.GSLT.LanguageDef.GauthierSkeletonExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.GauthierSkeletonExport.main arguments
