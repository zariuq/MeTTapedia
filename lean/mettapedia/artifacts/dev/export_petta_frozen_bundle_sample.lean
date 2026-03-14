import Algorithms.MeTTa.PeTTa.Lowering
import Mettapedia.Languages.MeTTa.PeTTa.Artifacts

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Artifacts

private def defaultOutDir : System.FilePath :=
  "/home/zar/claude/lean-projects/mettapedia/.artifacts/petta_frozen_bundle_sample"

private def sym (name : String) : Pattern := .apply name []

private def app (head : String) (args : List Pattern) : Pattern := .apply head args

private def sampleCfg : FrozenPeTTaConfig :=
  { rules :=
      [ { lhs := app "foo" [.fvar "X"]
          rhs := app "bar" [.fvar "X"] }
      , { lhs := app "tail" [.fvar "xs"]
          rhs := app "cons" [.fvar "x", .fvar "xs"] }
      , { lhs := app "mk" [.fvar "x"]
          rhs := app "wrap" [.fvar "x"] }
      , { lhs := app "use" [app "mk" [.fvar "x"], .fvar "y"]
          rhs := app "pair" [.fvar "x", .fvar "y"] } ]
    facts := []
    relationFacts := []
    builtinFacts := []
    maxSteps := 32
    maxNodes := 1024 }

def main (args : List String) : IO UInt32 := do
  let outDir :=
    match args with
    | dir :: _ => dir
    | [] => defaultOutDir.toString
  let outPath : System.FilePath := outDir
  let exportCode ← exportFrozenPeTTaArtifacts outPath sampleCfg
  if exportCode != 0 then
    pure exportCode
  else
    checkFrozenPeTTaArtifacts outPath sampleCfg
