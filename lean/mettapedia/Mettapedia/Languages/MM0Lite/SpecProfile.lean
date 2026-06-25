import Mettapedia.Languages.MM0Lite.LanguageDef

namespace Mettapedia.Languages.MM0Lite.SpecProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MM0Lite.LanguageDef

structure MM0LiteSyntaxProfile where
  schemaVersion : Nat := 1
  dialect : String := "mm0lite"
  languageName : String
  termLabels : List String
  rewriteNames : List String
  premiseRelations : List String
  syntaxTerminals : List String
deriving Repr, DecidableEq, BEq

private def sortStrings (xs : List String) : List String :=
  (xs.toArray.qsort (fun a b => a < b)).toList

private def terminalsOfRule (g : GrammarRule) : List String :=
  g.syntaxPattern.filterMap (fun
    | .terminal t => some t
    | .separator t => some t
    | _ => none)

private def premiseRelations : List String :=
  mm0Lite.rewrites.foldl
    (fun acc rw =>
      acc ++ rw.premises.filterMap (fun
        | .relationQuery rel _ => some rel
        | _ => none))
    []
  |> List.eraseDups
  |> sortStrings

def profile : MM0LiteSyntaxProfile :=
  { languageName := mm0Lite.name
    termLabels := sortStrings (mm0Lite.terms.map (·.label))
    rewriteNames := sortStrings (mm0Lite.rewrites.map (·.name))
    premiseRelations := premiseRelations
    syntaxTerminals := sortStrings ((mm0Lite.terms.foldl (fun acc g => acc ++ terminalsOfRule g) []).eraseDups) }

private def jsonEscape (s : String) : String :=
  s.foldl
    (fun acc c =>
      acc ++
      match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _ => String.singleton c)
    ""

private def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonNat (n : Nat) : String := toString n

private def jsonArr (xs : List String) : String :=
  "[" ++ String.intercalate "," (xs.map jsonStr) ++ "]"

def MM0LiteSyntaxProfile.renderJson (p : MM0LiteSyntaxProfile) : String :=
  "{"
    ++ "\"schema_version\":" ++ jsonNat p.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr p.dialect ++ ","
    ++ "\"language_name\":" ++ jsonStr p.languageName ++ ","
    ++ "\"term_labels\":" ++ jsonArr p.termLabels ++ ","
    ++ "\"rewrite_names\":" ++ jsonArr p.rewriteNames ++ ","
    ++ "\"premise_relations\":" ++ jsonArr p.premiseRelations ++ ","
    ++ "\"syntax_terminals\":" ++ jsonArr p.syntaxTerminals
  ++ "}"

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def MM0LiteSyntaxProfile.checksum (p : MM0LiteSyntaxProfile) : UInt64 :=
  checksumText p.renderJson

def MM0LiteSyntaxProfile.checksumString (p : MM0LiteSyntaxProfile) : String :=
  toString p.checksum

def exportProfile (outDir : System.FilePath) : IO UInt32 := do
  let p := profile
  let jsonPath := outDir / "mm0lite.syntax_profile.json"
  let checksumPath := outDir / "mm0lite.syntax_profile.checksum"
  IO.FS.createDirAll outDir
  IO.FS.writeFile jsonPath (p.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (p.checksumString ++ "\n")
  IO.println s!"exported mm0lite syntax-profile artifact to {outDir}"
  pure 0

def checkProfile (outDir : System.FilePath) : IO UInt32 := do
  let p := profile
  let jsonPath := outDir / "mm0lite.syntax_profile.json"
  let checksumPath := outDir / "mm0lite.syntax_profile.checksum"
  try
    let jsonText ← IO.FS.readFile jsonPath
    let checksumText ← IO.FS.readFile checksumPath
    let jsonOk := jsonText.trimAscii.toString == p.renderJson.trimAscii.toString
    let checksumOk := checksumText.trimAscii.toString == p.checksumString.trimAscii.toString
    if jsonOk && checksumOk then
      IO.println s!"[ok] mm0lite syntax-profile artifact matches at {outDir}"
      pure 0
    else
      IO.println s!"[drift] mm0lite syntax-profile artifact mismatch at {outDir}"
      if !jsonOk then
        IO.println s!"  json mismatch at {jsonPath}"
      if !checksumOk then
        IO.println s!"  checksum mismatch at {checksumPath}"
      pure 3
  catch e =>
    IO.println s!"mm0lite syntax-profile check failed: {e}"
    pure 2

end Mettapedia.Languages.MM0Lite.SpecProfile
