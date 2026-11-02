import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionCheck
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtomRead
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-! Print a canonical independent program payload through its authored source
grammar. The output file must not already exist. -/

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.Datalog
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def main (arguments : List String) : IO Unit := do
  let [inputPath,outputPath] := arguments | throw (IO.userError "expected program payload and source output paths")
  if ← (System.FilePath.mk outputPath).pathExists then throw (IO.userError "source output already exists")
  let .ok [atom] := SpaceSemantics.readSource (← IO.FS.readFile inputPath)
    | throw (IO.userError "expected one independent program payload")
  let some encoded := CettaWireAtom.decode? atom | throw (IO.userError "invalid program wire data")
  let some pattern := InferenceCettaWire.decodePattern encoded | throw (IO.userError "invalid program constructor data")
  let some program := IRCodec.program? pattern | throw (IO.userError "invalid independent program payload")
  unless SouffleDatalog.SourcePrinter.checkProgram program do
    throw (IO.userError "program is outside the declared source-printing profile")
  let text ← match SouffleDatalog.SourcePrinter.print? program with
    | .ok text => pure text
    | .error reason => throw (IO.userError reason)
  IO.FS.writeFile outputPath text
  IO.println s!"printed {program.statements.length} statements"
