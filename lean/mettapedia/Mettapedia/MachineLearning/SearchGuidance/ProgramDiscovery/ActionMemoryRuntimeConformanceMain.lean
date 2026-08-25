import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.ActionMemoryRuntimeConformance

/-!
# Verified-action-memory runtime conformance executable

The executable validates the semantic payload and independently hashes the
three Python implementations named by the fixed source layout.
-/

open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

private def usage : String :=
  "Usage: lake env lean --run " ++
    "Mettapedia/MachineLearning/SearchGuidance/ProgramDiscovery/" ++
    "ActionMemoryRuntimeConformanceMain.lean check <fixture.json> <repository-root>"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", fixturePath, repositoryRoot] =>
      let text ← IO.FS.readFile fixturePath
      match parseActionMemoryRuntimeFixture text with
      | .error message =>
          IO.eprintln s!"action-memory fixture parse failure: {message}"
          pure 1
      | .ok fixture =>
          if !fixture.check then
            IO.eprintln "action-memory fixture failed semantic conformance"
            pure 2
          else if !(← checkActionMemoryRuntimeSources repositoryRoot fixture) then
            IO.eprintln "action-memory fixture failed source-hash conformance"
            pure 3
          else
            IO.println "action-memory runtime fixture and source hashes conform"
            pure 0
  | _ =>
      IO.eprintln usage
      pure 4
