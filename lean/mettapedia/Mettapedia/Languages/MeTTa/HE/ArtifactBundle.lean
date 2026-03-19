import Mettapedia.Languages.MeTTa.HE.LookupPlan
import Mettapedia.Languages.MeTTa.HE.TransitionSpec
import Mettapedia.Languages.MeTTa.HE.RewriteIR
import Mettapedia.Languages.MeTTa.HE.ContractExport
import Mettapedia.Languages.MeTTa.HE.ScopeContract
import Mettapedia.Languages.MeTTa.HE.NativeProfile
import Mettapedia.Languages.MeTTa.HE.RuntimeContract
import Mettapedia.Languages.MeTTa.HE.SyntaxSpec
import MeTTailCore.Crypto.SHA256

/-!
# HE Artifact Bundle

Full-HE authority surface bundled with manifest integrity checking.
This is the single entry point for mettail-rust to load all HE contracts.

Schema v3 — mirrors PeTTa's `petta.manifest.json` pattern:
- manifest is the integrity root
- each artifact file's SHA-256 is recorded in the manifest
- Rust loads manifest first, validates everything else from it

## Contract-First Rule
Per `mettail-rust/CLAUDE.md`: profile chooses, contracts execute, Rust lowers
certified lanes. The manifest is how Rust discovers and validates the full
HE contract surface.

## Backend
MM2/MORK. Datalog/Ascent is deprecated and NOT referenced.
-/

namespace Mettapedia.Languages.MeTTa.HE.ArtifactBundle

open MeTTailCore.Crypto.SHA256

/-! ## Manifest Types -/

structure ManifestArtifactEntry where
  name : String
  sha256 : String
deriving Repr

structure HEBundleManifest where
  schemaVersion : Nat := 3
  dialect : String := "HE"
  semanticsVariant : String := "he-2026-03-standard"
  artifacts : List ManifestArtifactEntry := []
deriving Repr

/-! ## JSON Rendering -/

private def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | _ => String.singleton c) ""

private def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def renderManifestEntry (e : ManifestArtifactEntry) : String :=
  "{" ++ String.intercalate ","
    [ "\"name\":" ++ jsonStr e.name
    , "\"sha256\":" ++ jsonStr e.sha256
    ] ++ "}"

def HEBundleManifest.renderJson (m : HEBundleManifest) : String :=
  "{" ++ String.intercalate ","
    [ "\"schema_version\":" ++ toString m.schemaVersion
    , "\"dialect\":" ++ jsonStr m.dialect
    , "\"semantics_variant\":" ++ jsonStr m.semanticsVariant
    , "\"artifacts\":[" ++
        String.intercalate "," (m.artifacts.map renderManifestEntry) ++ "]"
    ] ++ "}"

/-! ## Artifact File Registry

All HE artifacts that belong to the bundle. Two directories:
- `artifacts/transition/` — most artifacts
- `artifacts/lookup/` — lookup plan
- `artifacts/syntax/` — syntax authority
-/

/-- Artifacts in `artifacts/transition/`. -/
private def transitionArtifactNames : List String :=
  [ "he.transition_spec.json"
  , "he.execution_contract.json"
  , "he.scope_contract.json"
  , "he.native_profile.json"
  , "he.runtime_contract.json"
  , "he.rewrite_ir.json"
  ]

/-- Artifacts in `artifacts/lookup/`. -/
private def lookupArtifactNames : List String :=
  [ "he.lookup_plan.json"
  ]

/-- Artifacts in `artifacts/syntax/`. -/
private def syntaxArtifactNames : List String :=
  [ "he.syntax_spec.json"
  , "he.grammar_spec.json"
  , "he-canonical.syntax_spec.json"
  , "he-canonical.grammar_spec.json"
  , "he.syntax_authority_profile.json"
  ]

/-! ## Manifest Export -/

private def digestFiles (dir : System.FilePath) (names : List String) :
    IO (List ManifestArtifactEntry) := do
  let mut entries : List ManifestArtifactEntry := []
  for name in names do
    let path := dir / name
    if ← path.pathExists then
      let content ← IO.FS.readFile path
      let digest := sha256Hex content
      entries := entries ++ [{ name := name, sha256 := digest }]
  pure entries

def exportHeManifest (transitionDir lookupDir syntaxDir : System.FilePath) : IO UInt32 := do
  let transEntries ← digestFiles transitionDir transitionArtifactNames
  let lookupEntries ← digestFiles lookupDir lookupArtifactNames
  let syntaxEntries ← digestFiles syntaxDir syntaxArtifactNames
  let allEntries := transEntries ++ lookupEntries ++ syntaxEntries
  let manifest : HEBundleManifest :=
    { schemaVersion := 3
    , dialect := "HE"
    , semanticsVariant := "he-2026-03-standard"
    , artifacts := allEntries }
  let manifestPath := transitionDir / "he.manifest.json"
  IO.FS.writeFile manifestPath (manifest.renderJson ++ "\n")
  IO.println s!"exported he manifest ({allEntries.length} artifacts) to {transitionDir}"
  pure 0

def checkHeManifest (transitionDir lookupDir syntaxDir : System.FilePath) : IO UInt32 := do
  let manifestPath := transitionDir / "he.manifest.json"
  if !(← manifestPath.pathExists) then
    IO.println "he manifest check skipped (he.manifest.json not found)"
    pure 0
  let transEntries ← digestFiles transitionDir transitionArtifactNames
  let lookupEntries ← digestFiles lookupDir lookupArtifactNames
  let syntaxEntries ← digestFiles syntaxDir syntaxArtifactNames
  let allEntries := transEntries ++ lookupEntries ++ syntaxEntries
  let expected : HEBundleManifest :=
    { schemaVersion := 3
    , dialect := "HE"
    , semanticsVariant := "he-2026-03-standard"
    , artifacts := allEntries }
  let storedText ← IO.FS.readFile manifestPath
  if storedText.trimAscii == expected.renderJson.trimAscii then
    IO.println s!"[ok] he manifest matches at {transitionDir}"
    pure 0
  else
    IO.println s!"[drift] he manifest mismatch at {transitionDir}"
    pure 3

section Canaries
#check @exportHeManifest
#check @checkHeManifest
end Canaries

end Mettapedia.Languages.MeTTa.HE.ArtifactBundle
