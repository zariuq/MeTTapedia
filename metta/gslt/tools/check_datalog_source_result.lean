import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutable
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtomRead
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-! Decode a completed emitted closure and compare output facts with an
external reference. This checker does not perform Datalog inference. -/

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.Languages.Datalog
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.OSLF.MeTTaIL Syntax

set_option maxRecDepth 32768

def readTerm (path : String) : IO Term := do
  let .ok [atom] := SpaceSemantics.readSource (← IO.FS.readFile path)
    | throw (IO.userError "expected one wire value")
  let some term := CettaWireAtom.decode? atom | throw (IO.userError "invalid wire value")
  pure term

def main (arguments : List String) : IO Unit := do
  let (payloadPath,resultPath,referencePath,relationName,singleRow) ← match arguments with
    | [payload,result,reference,relation] => pure (payload,result,reference,relation,false)
    | [payload,result,reference,relation,"--single-row"] => pure (payload,result,reference,relation,true)
    | _ => throw (IO.userError "expected program, runtime result, reference TSV, relation and optional --single-row")
  let some pattern := InferenceCettaWire.decodePattern (← readTerm payloadPath)
    | throw (IO.userError "invalid program wire")
  let some program := IRCodec.program? pattern | throw (IO.userError "invalid program")
  let .ok prepared := Executable.prepare program [] | throw (IO.userError "program preparation refused")
  let .application "SnapshotResult" [.symbol "SnapshotComplete",_,facts,_] ← readTerm resultPath
    | throw (IO.userError "runtime did not complete its closure")
  let some physical := InferenceCettaWire.decodeList InferenceCettaWire.decodePattern facts
    | throw (IO.userError "invalid runtime fact list")
  let some decoded := physical.mapM (Executable.decodeFact? prepared)
    | throw (IO.userError "runtime fact could not be decoded")
  let observed := (decoded.filter (·.relation == [relationName])).map fun fact =>
    if fact.values.isEmpty then "()" else String.intercalate "\t" (fact.values.map fun value => match value with
      | .symbol text => text | .number number => number.repr
      | .unsigned number => number.repr | .floating _ => "unsupported-float")
  let referenceText ← IO.FS.readFile referencePath
  let reference ← if singleRow then do
      unless referenceText.endsWith "\n" && observed.length == 1 do
        throw (IO.userError "single-row reference requires one observed fact and a final record terminator")
      pure [String.ofList referenceText.toList.dropLast]
    else pure (if referenceText.isEmpty then [] else
      if referenceText.endsWith "\n" then (referenceText.splitOn "\n").dropLast else referenceText.splitOn "\n")
  unless observed.toFinset == reference.toFinset do
    throw (IO.userError s!"output mismatch: runtime={observed.length}, reference={reference.length}")
  unless physical.length == physical.eraseDups.length do
    throw (IO.userError "runtime duplicated a fact in the canonical set")
  IO.println s!"checked {observed.length} output facts; complete and equal to the reference"
