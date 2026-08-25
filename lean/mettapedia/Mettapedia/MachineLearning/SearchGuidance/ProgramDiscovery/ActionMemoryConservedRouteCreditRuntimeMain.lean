import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.ActionMemoryConservedRouteCreditRuntime

/-!
# Conserved-route-credit runtime conformance executable

Validate the independently reconstructed transition and the fixed Python
source hashes carried by the runtime fixture.
-/

open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

private def usage : String :=
  "Usage: lake env lean --run " ++
    "Mettapedia/MachineLearning/SearchGuidance/ProgramDiscovery/" ++
    "ActionMemoryConservedRouteCreditRuntimeMain.lean check " ++
    "<fixture.json> <repository-root>"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", fixturePath, repositoryRoot] =>
      let fixtureText ← IO.FS.readFile fixturePath
      match parseConservedRouteCreditRuntimeFixture fixtureText with
      | .error message =>
          IO.eprintln s!"conserved-route-credit fixture parse failure: {message}"
          pure 1
      | .ok fixture =>
          if !fixture.check then
            IO.eprintln "conserved-route-credit semantic conformance failed"
            pure 2
          else if !(← checkConservedRouteCreditRuntimeSources
              repositoryRoot fixture) then
            IO.eprintln "conserved-route-credit source-hash conformance failed"
            pure 3
          else
            IO.println "conserved-route-credit runtime and source hashes conform"
            pure 0
  | _ =>
      IO.eprintln usage
      pure 4
