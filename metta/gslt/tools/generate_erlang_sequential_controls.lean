import Mettapedia.Languages.Erlang.SequentialExamples
import Mettapedia.Languages.Erlang.PatternProperties
import Mettapedia.Languages.Erlang.GuardProperties
import Lean.Data.Json.Printer

/-! Export independently assembled IR expectations and actual reference
machine results for native Erlang comparison. This is not a source frontend
or a substitute for the shared MeTTa backend. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

open Mettapedia.Languages.Erlang

def quoteAtom (name : String) : String := "'" ++ (name.replace "\\" "\\\\").replace "'" "\\'" ++ "'"

mutual
  def dataTerm? : Value → Option String
    | .literal (.integer value) => some (toString value)
    | .literal (.atom name) => some (quoteAtom name)
    | .literal .nil => some "[]"
    | .tuple fields => do pure ("{" ++ String.intercalate "," (← dataFields? fields) ++ "}")
    | .cons head tail => do pure ("[" ++ (← dataTerm? head) ++ "|" ++ (← dataTerm? tail) ++ "]")
    | .pid _ | .closure _ _ _ => none

  def dataFields? : List Value → Option (List String)
    | [] => some []
    | head :: tail => do pure ((← dataTerm? head) :: (← dataFields? tail))
end

def observation? : Result → Option String
  | .ok [value] => do pure ("{value," ++ (← dataTerm? value) ++ "}")
  | .error .badarith => some "{fault,badarith}"
  | .error .badarg => some "{fault,badarg}"
  | .error (.badfun value) => do pure ("{fault,{badfun," ++ (← dataTerm? value) ++ "}}")
  | _ => none

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected an output directory")
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  let mut rows := #[]
  let mut expected := ""
  for sample in SequentialExamples.examples do
    let direct := advance sample.program 5000 (begin sample.program)
    let resumed := (advance sample.program 13 (begin sample.program)).bind (advance sample.program 4987)
    let .ok (.halted result) := direct | throw (IO.userError (sample.name ++ ": sequential evaluation did not finish"))
    unless result == sample.expected && SequentialExamples.check sample do
      throw (IO.userError (sample.name ++ ": result or exact resumption disagreed"))
    let some observation := observation? sample.expected
      | throw (IO.userError (sample.name ++ ": no declared native observation"))
    expected := expected ++ "{" ++ quoteAtom sample.name ++ "," ++ observation ++ "}.\n"
    rows := rows.push (Lean.Json.mkObj [("name", .str sample.name), ("codeNodes", Lean.toJson sample.program.code.size),
      ("expected", .str observation), ("modelResult", .str (reprStr result)),
      ("resumed", .bool (match resumed with | .ok (.halted found) => found == result | _ => false))])
  IO.FS.writeFile (output / "expected.terms") expected
  IO.FS.writeFile (output / "model.json") (Lean.Json.mkObj [
    ("cases", .arr rows), ("unboundedIntegers", .bool true), ("multipleValuesAreTuples", .bool false),
    ("functionAndPidOrderingQualified", .bool false), ("fullPrimitiveProfileQualified", .bool false),
    ("sourceLoweringQualified", .bool false), ("emittedBackendQualified", .bool false),
    ("fullE0Qualified", .bool false)]).pretty
  IO.println s!"exported {rows.size} sequential controls"
