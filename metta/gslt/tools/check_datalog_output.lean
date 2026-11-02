import Mettapedia.Languages.Datalog.IRCodec
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtomRead

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.Datalog
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.OSLF.MeTTaIL Syntax Match

set_option maxRecDepth 32768

def binding? : Term → Option (String × Pattern)
  | .application "Binding" [.string name,value] => do pure (name,← InferenceCettaWire.decodePattern value)
  | _ => none

def fact? (dictionary : Bindings) (term : Term) : Option GroundFact := do
  let pattern ← InferenceCettaWire.decodePattern term
  IRCodec.groundFact? (applyBindings dictionary pattern)

def key? (dictionary : Bindings) : Term → Option DerivationKey
  | .application "SnapshotKey" [.natural ordinal,bindings,premises] => do
      let raw ← decodeList binding? bindings
      let values ← raw.mapM fun (name,pattern) => do
        pure (name,← IRCodec.value? (applyBindings dictionary pattern))
      pure ⟨ordinal,values,← decodeList (fact? dictionary) premises⟩
  | _ => none

def textValue : Value → String
  | .symbol text => text
  | .number value => value.repr
  | .unsigned value => value.repr
  | .floating word => toString word

def main (arguments : List String) : IO Unit := do
  let [dictionaryPath,resultPath,outputPath] := arguments | throw (IO.userError "expected dictionary, native result and output directory")
  let .ok [dictionaryAtom] := SpaceSemantics.readSource (← IO.FS.readFile dictionaryPath)
    | throw (IO.userError "invalid dictionary text")
  let some dictionaryWire := CettaWireAtom.decode? dictionaryAtom | throw (IO.userError "invalid dictionary wire")
  let some dictionary := decodeList binding? dictionaryWire | throw (IO.userError "invalid dictionary bindings")
  let .ok results := SpaceSemantics.readSource (← IO.FS.readFile resultPath) | throw (IO.userError "invalid native result text")
  let selected := results.filterMap fun atom => match atom with
    | .expression [.symbol "OrdinaryDatalog",result] => some result
    | _ => none
  let [result] := selected | throw (IO.userError "missing or duplicated native closure result")
  let some (.application "SnapshotResult" [.symbol "SnapshotComplete",.natural rounds,facts,keys]) := CettaWireAtom.decode? result
    | throw (IO.userError "execution is pending or faulted")
  let some facts := decodeList (fact? dictionary) facts | throw (IO.userError "fact decoding failed")
  let some keys := decodeList (key? dictionary) keys | throw (IO.userError "logical-key decoding failed")
  let output := System.FilePath.mk outputPath
  IO.FS.createDirAll output
  let declaredRelations := dictionary.filterMap fun (_,pattern) => IRCodec.relation? pattern
  for relation in (declaredRelations ++ facts.map (·.relation)).eraseDups do
    let rows := (facts.filter (·.relation == relation)).map fun fact =>
      if fact.values.isEmpty then "()" else String.intercalate "\t" (fact.values.map textValue)
    IO.FS.writeFile (output / (String.intercalate "." relation ++ ".csv"))
      (if rows.isEmpty then "" else String.intercalate "\n" rows ++ "\n")
  IO.FS.writeFile (output / "keys.txt") (reprStr keys ++ "\n")
  IO.println s!"complete: rounds={rounds}, facts={facts.length}, keys={keys.length}"
