import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIREmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontend
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendSource
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionCheck
import Mettapedia.Languages.Datalog.FactInputCorrespondence
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassSearch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

/-! Compile an explicitly selected shared-parser packet for ordinary source.
The emitter prepares rules and scalar operations; inference runs in MeTTa. -/

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.Languages.Datalog
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.OSLF.MeTTaIL Syntax

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def inputs (program : Program) (directory : System.FilePath) : IO (List GroundFact) := do
  let mut facts := []
  for statement in program.statements do
    if let .input name := statement then
      let some types := ProgramStatic.signature program name | throw (IO.userError "undeclared input")
      let text ← IO.FS.readFile (directory / (String.intercalate "." name ++ ".facts"))
      let some decoded := FactInput.read? name types text
        | throw (IO.userError s!"invalid input record or scalar for {String.intercalate "." name}")
      facts := facts ++ decoded
  pure facts

def main (arguments : List String) : IO Unit := do
  let [sourcePath,packetPath,inputDirectory,outputPath,entry] := arguments
    | throw (IO.userError "expected source, selected packet, fact directory, output and entry name")
  let input ← IO.FS.readFile sourcePath
  let packet ← IO.FS.readFile packetPath
  let .ok [tree] := SpaceSemantics.readSource packet | throw (IO.userError "parser packet is malformed or ambiguous")
  let program ← match SouffleDatalog.Frontend.read input tree with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  let seeds ← inputs program inputDirectory
  let prepared ← match Executable.prepare program seeds with
    | .ok prepared => pure prepared
    | .error reason => throw (IO.userError reason)
  unless SouffleDatalog.SourcePrinter.checkProgram program do
    throw (IO.userError "program is outside the declared source-printing profile")
  let canonical ← match SouffleDatalog.SourcePrinter.print? program with
    | .ok text => pure text
    | .error reason => throw (IO.userError s!"source printing refused: {reason}")
  let emitted ← match DatalogIR.Emission.emit prepared entry with
    | .ok result => pure result
    | .error reason => throw (IO.userError reason)
  IO.FS.writeFile outputPath emitted.definitions
  IO.FS.writeFile (outputPath ++ ".dictionary.metta") emitted.dictionary
  IO.FS.writeFile (outputPath ++ ".source.dl") canonical
  IO.FS.writeFile (outputPath ++ ".program.metta") emitted.programPayload
  IO.println s!"compiled ordinary Datalog: {program.statements.length} statements, {prepared.compiled.rewrites.length} rules, {seeds.length} input facts"
