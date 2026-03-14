import Mettapedia.Languages.MeTTa.PeTTa.ArtifactBundle

/-!
# Export Dialect-Static PeTTa Native Profile

Exports the native profile with an empty PeTTaSpace (no user rules).
This produces:
  - rule_profiles: []  (empty — no program rules)
  - contract_profiles: fully populated (kernel-certified catalog)
  - scope_profiles: fully populated (kernel-certified catalog)
  - boundary_profiles: fully populated (kernel-certified catalog)

The dialect-static sections are real certified data from Lean.
Rule profiles are program-specific and require a per-program AOT export.
-/

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Artifacts

private def defaultOutDir : System.FilePath :=
  "/home/zar/claude/lean-projects/mettapedia/artifacts/transition"

/-- Empty PeTTaSpace: no facts, no rules.
    Produces the dialect-static native profile slice. -/
private def emptySpace : PeTTaSpace :=
  ⟨[], []⟩

def main (args : List String) : IO UInt32 := do
  let outDir :=
    match args with
    | dir :: _ => dir
    | [] => defaultOutDir.toString
  let outPath : System.FilePath := outDir
  IO.println "exporting dialect-static PeTTa artifact bundle (empty space)..."
  let exportCode ← exportPeTTaArtifacts outPath emptySpace .boundaryAware
  if exportCode != 0 then
    IO.println s!"export failed with code {exportCode}"
    pure exportCode
  else
    IO.println "verifying exported artifacts..."
    let checkCode ← checkPeTTaArtifacts outPath emptySpace .boundaryAware
    if checkCode != 0 then
      IO.println s!"verification failed with code {checkCode}"
      pure checkCode
    else
      IO.println "[ok] dialect-static native profile exported and verified"
      pure 0
