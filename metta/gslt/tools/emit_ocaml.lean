import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlExecutionData
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! Compile an explicitly selected ordinary-source packet through independent
OCaml IR and the shared emitter. Evaluation remains in the emitted runtime. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa

def main (arguments : List String) : IO Unit := do
  let [sourcePath, packetPath, outputPath, entry] := arguments
    | throw (IO.userError "expected source, selected packet, output and entry name")
  if ← (System.FilePath.mk outputPath).pathExists then
    throw (IO.userError "output already exists")
  let .ok [.expression [.symbol "result", tree, .symbol "nil"]] :=
      SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "expected exactly one explicitly selected whole-input result")
  let retained ← match GoldCoreSourceLowering.ocaml (← IO.FS.readFile sourcePath) tree with
    | .ok retained => pure retained
    | .error reason => throw (IO.userError reason)
  let program := retained.lowered
  let prepared ← match OCamlCompilation.prepare program with
    | .ok prepared => pure prepared
    | .error reason => throw (IO.userError reason)
  let emitted ← match OCamlCompilation.ExecutionData.emitText? prepared entry with
    | .ok emitted => pure emitted
    | .error reason => throw (IO.userError reason)
  IO.FS.writeFile outputPath emitted
  IO.println s!"compiled source: {program.code.size} instructions"
