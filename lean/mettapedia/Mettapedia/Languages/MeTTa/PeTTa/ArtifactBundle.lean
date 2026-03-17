import Mettapedia.Languages.MeTTa.PeTTa.LookupPlan
import Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.PeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIR
import Mettapedia.Languages.MeTTa.PeTTa.SemanticBundle
import MeTTailCore.Crypto.SHA256

/-!
# PeTTa Artifact Bundle

Pure spec-side artifact bundle over `PeTTaSpace`.

Schema v3 adds:
- `petta.manifest.json` — bundle manifest with SHA-256 digests
- `semantics_variant` in both manifest and native profile
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.Artifacts

open MeTTailCore.Crypto.SHA256

/-! ## §1 Manifest Types -/

/-- An entry in the bundle manifest listing one artifact file and its SHA-256 digest. -/
structure ManifestArtifactEntry where
  name : String
  sha256 : String
  deriving Repr

/-- The top-level bundle manifest. This is the integrity root for the artifact bundle.
    Rust loads and validates this first, then checks each artifact file's SHA-256
    against the manifest. -/
structure PeTTaBundleManifest where
  schemaVersion : Nat := 3
  dialect : String := "PeTTa"
  semanticsVariant : String := "petta-2026-03-boundary-aware"
  stage : String := "boundary_aware"
  programFingerprint : Option String := none
  artifacts : List ManifestArtifactEntry := []
  deriving Repr

/-! ## §2 Manifest JSON Rendering -/

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

def PeTTaBundleManifest.renderJson (m : PeTTaBundleManifest) : String :=
  "{" ++ String.intercalate ","
    [ "\"schema_version\":" ++ toString m.schemaVersion
    , "\"dialect\":" ++ jsonStr m.dialect
    , "\"semantics_variant\":" ++ jsonStr m.semanticsVariant
    , "\"stage\":" ++ jsonStr m.stage
    , match m.programFingerprint with
      | some fp => "\"program_fingerprint\":" ++ jsonStr fp
      | none => "\"program_fingerprint\":null"
    , "\"artifacts\":[" ++
        String.intercalate "," (m.artifacts.map renderManifestEntry) ++ "]"
    ] ++ "}"

/-! ## §3 Artifact File Names -/

private def artifactFileNames : List String :=
  [ "petta.lookup_plan.json"
  , "petta.execution_contract.json"
  , "petta.scope_contract.json"
  , "petta.transition_spec.json"
  , "petta.rewrite_ir.json"
  , "petta.native_profile.json"
  ]

/-! ## §4 Manifest Export -/

/-- Compute SHA-256 digests of all artifact files and write `petta.manifest.json`. -/
private def writeManifest (outDir : System.FilePath)
    (programFingerprint : Option String := none) : IO UInt32 := do
  let mut entries : List ManifestArtifactEntry := []
  for name in artifactFileNames do
    let path := outDir / name
    if ← path.pathExists then
      let content ← IO.FS.readFile path
      let digest := sha256Hex content
      entries := entries ++ [{ name := name, sha256 := digest }]
  let manifest : PeTTaBundleManifest :=
    { schemaVersion := 3
    , dialect := "PeTTa"
    , semanticsVariant := "petta-2026-03-boundary-aware"
    , stage := "boundary_aware"
    , programFingerprint := programFingerprint
    , artifacts := entries }
  let manifestPath := outDir / "petta.manifest.json"
  IO.FS.writeFile manifestPath (manifest.renderJson ++ "\n")
  IO.println s!"exported petta manifest ({entries.length} artifacts) to {outDir}"
  pure 0

/-- Verify manifest digests against artifact files on disk. -/
private def checkManifest (outDir : System.FilePath)
    (programFingerprint : Option String := none) : IO UInt32 := do
  let manifestPath := outDir / "petta.manifest.json"
  if !(← manifestPath.pathExists) then
    IO.println "manifest check skipped (petta.manifest.json not found)"
    pure 0  -- not an error; manifest is optional during transition
  -- Rebuild expected manifest and compare
  let mut entries : List ManifestArtifactEntry := []
  for name in artifactFileNames do
    let path := outDir / name
    if ← path.pathExists then
      let content ← IO.FS.readFile path
      let digest := sha256Hex content
      entries := entries ++ [{ name := name, sha256 := digest }]
  let expected : PeTTaBundleManifest :=
    { schemaVersion := 3
    , dialect := "PeTTa"
    , semanticsVariant := "petta-2026-03-boundary-aware"
    , stage := "boundary_aware"
    , programFingerprint := programFingerprint
    , artifacts := entries }
  let storedText ← IO.FS.readFile manifestPath
  if storedText.trimAscii == expected.renderJson.trimAscii then
    IO.println s!"[ok] petta manifest matches at {outDir}"
    pure 0
  else
    IO.println s!"[FAIL] petta manifest mismatch at {outDir}"
    pure 3

/-! ## §5 Lookup Plan (unchanged) -/

private def writeLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  let artifact := Mettapedia.Languages.MeTTa.PeTTa.LookupPlan.pettaLookupPlanArtifact
  let jsonPath := outDir / "petta.lookup_plan.json"
  let checksumPath := outDir / "petta.lookup_plan.checksum"
  IO.FS.createDirAll outDir
  IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
  pure 0

private def checkLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  let artifact := Mettapedia.Languages.MeTTa.PeTTa.LookupPlan.pettaLookupPlanArtifact
  let jsonPath := outDir / "petta.lookup_plan.json"
  let checksumPath := outDir / "petta.lookup_plan.checksum"
  try
    let jsonText ← IO.FS.readFile jsonPath
    let checksumText ← IO.FS.readFile checksumPath
    let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
    let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
    if jsonOk && checksumOk then
      pure 0
    else
      pure 3
  catch _ =>
    pure 2

/-! ## §6 Bundle Export + Check -/

def exportPeTTaArtifacts (outDir : System.FilePath) (s : PeTTaSpace)
    (stage : Mettapedia.Languages.MeTTa.PeTTa.StageIndex.PeTTaStage :=
       .boundaryAware) : IO UInt32 := do
  let a ← writeLookupPlan outDir
  let b ← Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract.exportPeTTaExecutionContract outDir
  let c ← Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.exportPeTTaScopeContract outDir
  let d ← Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec.exportPeTTaTransitionSpec outDir s
  let e ← Mettapedia.Languages.MeTTa.PeTTa.RewriteIR.exportPeTTaRewriteIR outDir s
  -- Native profile export (requires both ts and ir artifacts)
  let f ← match Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec.derivePeTTaTransitionSpec? s,
                Mettapedia.Languages.MeTTa.PeTTa.RewriteIR.derivePeTTaRewriteIR? s with
    | .ok ts, .ok ir =>
        Mettapedia.Languages.MeTTa.PeTTa.SemanticBundle.exportPeTTaNativeProfile
          outDir s stage ts ir
    | _, _ =>
        IO.println "petta native-profile export skipped (ts/ir derivation failed)"
        pure 2
  -- Write manifest AFTER all artifacts are on disk
  let g ← if a == 0 && b == 0 && c == 0 && d == 0 && e == 0 && f == 0 then
    writeManifest outDir
  else
    pure 2
  if a == 0 && b == 0 && c == 0 && d == 0 && e == 0 && f == 0 && g == 0 then
    IO.println s!"exported petta artifact bundle to {outDir}"
    pure 0
  else
    pure 2

/-- Check all PeTTa artifacts for consistency with the current spec.

    The `stage` parameter defaults to `.boundaryAware` — the fullest stage,
    matching the default used by `exportPeTTaArtifacts`.  Tests or research
    may pass other stages explicitly. -/
def checkPeTTaArtifacts (outDir : System.FilePath) (s : PeTTaSpace)
    (stage : Mettapedia.Languages.MeTTa.PeTTa.StageIndex.PeTTaStage :=
       .boundaryAware) : IO UInt32 := do
  let a ← checkLookupPlan outDir
  let b ← Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract.checkPeTTaExecutionContract outDir
  let c ← Mettapedia.Languages.MeTTa.PeTTa.ScopeContract.checkPeTTaScopeContract outDir
  let d ← Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec.checkPeTTaTransitionSpec outDir s
  let e ← Mettapedia.Languages.MeTTa.PeTTa.RewriteIR.checkPeTTaRewriteIR outDir s
  let f ← match Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec.derivePeTTaTransitionSpec? s,
                Mettapedia.Languages.MeTTa.PeTTa.RewriteIR.derivePeTTaRewriteIR? s with
    | .ok ts, .ok ir =>
        Mettapedia.Languages.MeTTa.PeTTa.SemanticBundle.checkPeTTaNativeProfile
          outDir s stage ts ir
    | _, _ =>
        IO.println "native-profile check skipped (ts/ir derivation failed)"
        pure 2
  let g ← checkManifest outDir
  if a == 0 && b == 0 && c == 0 && d == 0 && e == 0 && f == 0 && g == 0 then
    IO.println s!"[ok] petta artifact bundle matches at {outDir}"
    pure 0
  else
    pure 3

end Mettapedia.Languages.MeTTa.PeTTa.Artifacts
