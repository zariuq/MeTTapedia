import Mettapedia.Languages.MM0.SyntaxSpec
import MeTTailCore.Crypto.SHA256

/-!
# MM0 Syntax Metadata Bundle

Artifact export for descriptive MM0 syntax metadata.
Exports JSON records with SHA-256 checksums.

Does NOT replace MM0Lite (which is a minimal LanguageDef formalization).
This bundle is not an executable parser, a proof verifier, a language
authority, or evidence that NIK hosts MM0.
-/

namespace Mettapedia.Languages.MM0.ArtifactBundle

open Mettapedia.Languages.MM0.SyntaxMetadata

structure MM0BundleManifest where
  schemaVersion : Nat := 1
  language : String := "MM0"
  dialect : String := "full-surface-metadata"
  description : String :=
    "Descriptive MM0 syntax metadata. The upstream language uses two-stage parsing: " ++
    "primary (.mm0 file structure) + secondary (math-string notation). " ++
    "Executable parsing, MMB verification, and hosting are outside this bundle."
  artifacts : List (String × String)  -- (path, sha256)
deriving Repr, Lean.ToJson, Lean.FromJson

def defaultOutDir : System.FilePath := "artifacts/mm0-syntax-metadata"

def exportMM0ManifestBundle (outDir : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll outDir
  -- Export descriptive syntax metadata.
  exportMM0SyntaxMetadataArtifacts outDir
  -- Compute manifest digests from canonical JSON payloads
  let files := [
    "mm0.primary_syntax_metadata.json",
    "mm0.secondary_parse_metadata.json",
    "mm0.syntax_metadata_profile.json"
  ]
  let mut artifacts : List (String × String) := []
  for f in files do
    let path := outDir / f
    if ← path.pathExists then
      let content ← IO.FS.readFile path
      let hash := MeTTailCore.Crypto.SHA256.sha256Hex content
      artifacts := artifacts ++ [(f, hash)]
  -- Write manifest
  let manifest : MM0BundleManifest :=
    { artifacts := artifacts }
  IO.FS.writeFile (outDir / "mm0-syntax-metadata.manifest.json")
    (Lean.toJson manifest).pretty
  IO.println s!"MM0 syntax metadata: exported {artifacts.length} artifacts to {outDir}"
  pure 0

def checkMM0ManifestBundle (outDir : System.FilePath) : IO UInt32 := do
  let ok ← checkMM0SyntaxMetadataArtifacts outDir
  if !ok then
    IO.eprintln s!"MM0 syntax metadata: missing artifacts in {outDir}"
    return 1
  let files := [
    "mm0.primary_syntax_metadata.json",
    "mm0.secondary_parse_metadata.json",
    "mm0.syntax_metadata_profile.json"
  ]
  let mut artifacts : List (String × String) := []
  for f in files do
    let jsonPath := outDir / f
    let checksumPath := outDir / (f ++ ".checksum")
    let content ← IO.FS.readFile jsonPath
    let checksum ← IO.FS.readFile checksumPath
    let expected := MeTTailCore.Crypto.SHA256.sha256Hex content
    if checksum.trimAscii.toString != expected.trimAscii.toString then
      IO.eprintln s!"MM0 full: checksum drift at {checksumPath}"
      return 2
    artifacts := artifacts ++ [(f, expected)]
  let expectedManifest : MM0BundleManifest := { artifacts := artifacts }
  let manifestPath := outDir / "mm0-syntax-metadata.manifest.json"
  let storedManifest ← IO.FS.readFile manifestPath
  if storedManifest.trimAscii.toString != (Lean.toJson expectedManifest).pretty.trimAscii.toString then
    IO.eprintln s!"MM0 full: manifest drift at {manifestPath}"
    return 3
  IO.println s!"MM0 syntax metadata: artifacts and manifest match at {outDir}"
  pure 0

end Mettapedia.Languages.MM0.ArtifactBundle
