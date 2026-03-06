import Mettapedia.Languages.IMP.LanguageDef

namespace Mettapedia.Languages.IMP.SpecProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.IMP.LanguageDef

structure IMPSyntaxProfile where
  schemaVersion : Nat := 1
  dialect : String := "imp"
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
  imp.rewrites.foldl
    (fun acc rw =>
      acc ++ rw.premises.filterMap (fun
        | .relationQuery rel _ => some rel
        | _ => none))
    []
  |> List.eraseDups
  |> sortStrings

def profile : IMPSyntaxProfile :=
  { languageName := imp.name
    termLabels := sortStrings (imp.terms.map (·.label))
    rewriteNames := sortStrings (imp.rewrites.map (·.name))
    premiseRelations := premiseRelations
    syntaxTerminals := sortStrings ((imp.terms.foldl (fun acc g => acc ++ terminalsOfRule g) []).eraseDups) }

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

def IMPSyntaxProfile.renderJson (p : IMPSyntaxProfile) : String :=
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

def IMPSyntaxProfile.checksum (p : IMPSyntaxProfile) : UInt64 :=
  checksumText p.renderJson

def IMPSyntaxProfile.checksumString (p : IMPSyntaxProfile) : String :=
  toString p.checksum

def exportProfile (outDir : System.FilePath) : IO UInt32 := do
  let p := profile
  let jsonPath := outDir / "imp.syntax_profile.json"
  let checksumPath := outDir / "imp.syntax_profile.checksum"
  IO.FS.createDirAll outDir
  IO.FS.writeFile jsonPath (p.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (p.checksumString ++ "\n")
  IO.println s!"exported imp syntax-profile artifact to {outDir}"
  pure 0

def checkProfile (outDir : System.FilePath) : IO UInt32 := do
  let p := profile
  let jsonPath := outDir / "imp.syntax_profile.json"
  let checksumPath := outDir / "imp.syntax_profile.checksum"
  try
    let jsonText ← IO.FS.readFile jsonPath
    let checksumText ← IO.FS.readFile checksumPath
    let jsonOk := jsonText.trimAscii.toString == p.renderJson.trimAscii.toString
    let checksumOk := checksumText.trimAscii.toString == p.checksumString.trimAscii.toString
    if jsonOk && checksumOk then
      IO.println s!"[ok] imp syntax-profile artifact matches at {outDir}"
      pure 0
    else
      IO.println s!"[drift] imp syntax-profile artifact mismatch at {outDir}"
      if !jsonOk then
        IO.println s!"  json mismatch at {jsonPath}"
      if !checksumOk then
        IO.println s!"  checksum mismatch at {checksumPath}"
      pure 3
  catch e =>
    IO.println s!"imp syntax-profile check failed: {e}"
    pure 2

end Mettapedia.Languages.IMP.SpecProfile
