import Mettapedia.Languages.MM0.SyntaxSpec
import MeTTailCore.Crypto.SHA256

/-!
# Full MM0 Artifact Bundle

Artifact export for the full MM0 language, following the HE pattern.
Exports syntax authority artifacts to JSON with SHA-256 checksums.

Does NOT replace MM0Lite (which is a minimal LanguageDef formalization).
This is the full-language syntax authority for the complete MM0 spec.
-/

namespace Mettapedia.Languages.MM0.ArtifactBundle

open Mettapedia.Languages.MM0.SyntaxSpec

structure MM0BundleManifest where
  schemaVersion : Nat := 1
  language : String := "MM0"
  dialect : String := "full"
  description : String :=
    "Full MM0 syntax authority artifacts. Two-stage parsing: " ++
    "primary (.mm0 file structure) + secondary (math-string notation). " ++
    "Trust boundary: MMB binary format verified by mm0-c stack machine."
  artifacts : List (String × String)  -- (path, sha256)
deriving Repr, Lean.ToJson, Lean.FromJson

def defaultOutDir : System.FilePath := "artifacts/mm0-full"

def exportMM0ManifestBundle (outDir : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll outDir
  -- Export syntax artifacts
  exportMM0SyntaxArtifacts outDir
  -- Compute manifest digests from canonical JSON payloads
  let files := [
    "mm0.syntax_spec.json",
    "mm0.secondary_parse_contract.json",
    "mm0.syntax_authority_profile.json"
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
  IO.FS.writeFile (outDir / "mm0-full.manifest.json")
    (Lean.toJson manifest).pretty
  IO.println s!"MM0 full: exported {artifacts.length} artifacts to {outDir}"
  pure 0

def checkMM0ManifestBundle (outDir : System.FilePath) : IO UInt32 := do
  let ok ← checkMM0SyntaxArtifacts outDir
  if !ok then
    IO.eprintln s!"MM0 full: missing artifacts in {outDir}"
    return 1
  let files := [
    "mm0.syntax_spec.json",
    "mm0.secondary_parse_contract.json",
    "mm0.syntax_authority_profile.json"
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
  let manifestPath := outDir / "mm0-full.manifest.json"
  let storedManifest ← IO.FS.readFile manifestPath
  if storedManifest.trimAscii.toString != (Lean.toJson expectedManifest).pretty.trimAscii.toString then
    IO.eprintln s!"MM0 full: manifest drift at {manifestPath}"
    return 3
  IO.println s!"MM0 full: artifacts and manifest match at {outDir}"
  pure 0

end Mettapedia.Languages.MM0.ArtifactBundle
