import Mettapedia.Languages.MeTTa.PeTTa.ArtifactBundle

/-!
# Export Sample Full PeTTa Native Profile

Exports a complete native profile from a small concrete PeTTaSpace
with representative rules covering all semantic classes:
  - ordinary_forward (no premises, no compat-head)
  - premise_aware (has spaceMatch premise)
  - compat_head (constraint argument in LHS)

This is the end-to-end seam test: Lean constructs a program, derives
the full semantic bundle, and exports the native profile. Rust loads
it and runs Shadow-mode comparison.
-/

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Artifacts
open Mettapedia.OSLF.MeTTaIL.Syntax

private def defaultOutDir : System.FilePath :=
  "/home/zar/claude/lean-projects/mettapedia/.artifacts/petta_native_profile_sample"

/-- Sample PeTTaSpace with representative rules. -/
private def sampleSpace : PeTTaSpace :=
  { facts := []
    rules :=
      [ -- ordinary_forward: simple rewrite, no premises
        { name := "ordinary"
          typeContext := []
          premises := []
          left := .apply "foo" [.fvar "X"]
          right := .apply "bar" [.fvar "X"] }
      , -- another ordinary_forward: multi-arg, RHS has fresh vars
        { name := "swap_pair"
          typeContext := []
          premises := []
          left := .apply "swap" [.fvar "A", .fvar "B"]
          right := .apply "pair" [.fvar "B", .fvar "A"] }
      , -- premise_aware: has a spaceMatch premise
        { name := "with_premise"
          typeContext := []
          premises :=
            [ Premise.relationQuery "spaceMatch"
                [.fvar "X", .fvar "Y", .fvar "Z"] ]
          left := .apply "lookup" [.fvar "X"]
          right := .fvar "Z" }
      ] }

def main (args : List String) : IO UInt32 := do
  let outDir :=
    match args with
    | dir :: _ => dir
    | [] => defaultOutDir.toString
  let outPath : System.FilePath := outDir
  IO.println "exporting sample PeTTa artifact bundle (3 representative rules)..."
  let exportCode ← exportPeTTaArtifacts outPath sampleSpace .boundaryAware
  if exportCode != 0 then
    IO.println s!"export failed with code {exportCode}"
    pure exportCode
  else
    IO.println "verifying exported artifacts..."
    let checkCode ← checkPeTTaArtifacts outPath sampleSpace .boundaryAware
    if checkCode != 0 then
      IO.println s!"verification failed with code {checkCode}"
      pure checkCode
    else
      IO.println "[ok] sample native profile exported and verified"
      pure 0
