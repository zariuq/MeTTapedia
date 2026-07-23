import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.ActiveProbing

/-!
# Active-probe supplement fixture exporter

This executable writes or checks the canonical supplement envelope using the
same Lean renderer and SHA-256 pins as the formal selector.
-/

open Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

private def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  lake env lean --run Mettapedia/MachineLearning/NeuralNetworks/UtilizationAtlas/ActiveProbeSupplementFixtureMain.lean write <output.json>"
    , "  lake env lean --run Mettapedia/MachineLearning/NeuralNetworks/UtilizationAtlas/ActiveProbeSupplementFixtureMain.lean check <fixture.json>"
    ]

/-- Write or independently check the active-probe supplement fixture. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["write", path] =>
      IO.FS.writeFile path renderActiveProbeSupplementFixture
      pure 0
  | ["check", path] =>
      let actual ← IO.FS.readFile path
      if actual = renderActiveProbeSupplementFixture then
        pure 0
      else
        IO.eprintln
          "active-probe supplement fixture differs from its canonical Lean rendering"
        pure 1
  | _ =>
      IO.eprintln usage
      pure 2
