import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangExecutionData
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! Emit the existing Erlang step controller from a selected textual Core
entry. Actor operations remain explicit requests for the existing actor/rho
runtime. This does not select a schedule or claim complete exploration. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa

def main (arguments : List String) : IO Unit := do
  let sourcePath :: packetPath :: outputPath :: name :: entry :: integerArguments := arguments
    | throw (IO.userError "expected source, selected packet, output, emitter name, entry and optional integers")
  if ← (System.FilePath.mk outputPath).pathExists then throw (IO.userError "output already exists")
  let .ok [.expression [.symbol "result", tree, .symbol "nil"]] :=
      SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "expected one explicitly selected whole-input result")
  let values ← integerArguments.mapM fun text => do
    let some number := text.toInt? | throw (IO.userError "expected integer entry arguments")
    pure (Mettapedia.Languages.Erlang.Value.literal (.integer number))
  let retained ← match GoldCoreSourceLowering.erlang (← IO.FS.readFile sourcePath) tree entry values with
    | .ok retained => pure retained
    | .error reason => throw (IO.userError reason)
  let compiled := retained.lowered
  let prepared ← match ErlangCompilation.prepare compiled.program with
    | .ok prepared => pure prepared
    | .error reason => throw (IO.userError reason)
  let emitted ← match ErlangCompilation.ExecutionData.emitText? prepared name with
    | .ok emitted => pure emitted
    | .error reason => throw (IO.userError reason)
  IO.FS.writeFile outputPath emitted
  IO.println s!"compiled {compiled.moduleName}: {compiled.program.code.size} instructions, {compiled.retained.length} retained functions"
