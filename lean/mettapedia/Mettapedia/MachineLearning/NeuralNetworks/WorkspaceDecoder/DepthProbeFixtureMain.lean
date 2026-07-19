import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Predictions

/-!
# Depth-probe schema fixture exporter

This executable writes or checks the canonical schema envelope exported by
`Predictions`.  Keeping both modes in Lean makes the checked artifact use the
same renderer and SHA-256 pin as the formal source.
-/

open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

private def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  lake env lean --run Mettapedia/MachineLearning/NeuralNetworks/WorkspaceDecoder/DepthProbeFixtureMain.lean write <output.json>"
    , "  lake env lean --run Mettapedia/MachineLearning/NeuralNetworks/WorkspaceDecoder/DepthProbeFixtureMain.lean check <fixture.json>"
    ]

/-- Write or independently check the hash-pinned depth-probe schema fixture. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["write", path] =>
      IO.FS.writeFile path renderDepthProbeSchemaFixture
      pure 0
  | ["check", path] =>
      let actual ← IO.FS.readFile path
      if actual = renderDepthProbeSchemaFixture then
        pure 0
      else
        IO.eprintln "depth-probe schema fixture differs from its canonical Lean rendering"
        pure 1
  | _ =>
      IO.eprintln usage
      pure 2
