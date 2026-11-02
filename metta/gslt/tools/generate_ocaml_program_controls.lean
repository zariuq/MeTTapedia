import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlExecutionData
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
import Mettapedia.Languages.OCaml.Examples
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! Prepared indexed programs through the native controller and shared GSLT
step machine. Expected values/faults are independent fixtures also checked in
the OCaml reference. Ordinary-source lowering remains a separate contract. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.Languages
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def fault (error : OCaml.Fault) : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern := match error with
  | .divisionByZero => node "MlDivisionByZero"
  | .matchFailure => node "MlMatchFailure"
  | .functionalComparison => node "MlFunctionalComparison"

def generate (directory label : String) (program : OCaml.Program) (observation : OCaml.Result) : IO Unit := do
  let .ok prepared := prepare program | throw (IO.userError "OCaml preparation refused")
  let .ok emitted := ExecutionData.emitText? prepared "ml-program"
    | throw (IO.userError "OCaml controller emission refused")
  let expected := match observation with
    | .ok datum => node "MlDone" [value datum]
    | .error error => node "MlFault" [fault error]
  let expected := CettaWire.Term.render (InferenceCettaWire.encodePattern expected)
  let controls :=
    "!(let* (($begun (ml-program:begin))" ++
    " ($direct (gslt:ml:advance 20000 50 $begun))" ++
    " ($first (gslt:ml:advance 37 50 $begun))" ++
    " ($resumed (gslt:ml:advance 19963 50 $first)))" ++
    " (case (gslt:ml:result $direct) (((MlResult $phase $state $epochs $current)" ++
    " (println! (OCamlProgramControl " ++ reprStr label ++
    " (== $phase MlComplete) (== $state (quote " ++ expected ++ ")) (== $direct $resumed)" ++
    " (gslt:automata:length $epochs)))))))\n"
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") controls
  IO.println s!"prepared {label}: {program.code.size} instructions"

def main (arguments : List String) : IO Unit := do
  let directory :: label :: sourceArguments := arguments
    | throw (IO.userError "expected output, example name and optional source/selected-packet paths")
  let some sample := (OCaml.Examples.examples ++ OCaml.Examples.structuralExamples).find? (·.name == label)
    | throw (IO.userError "unknown independent observation fixture")
  let program ← match sourceArguments with
    | [] => pure sample.program
    | [sourcePath, packetPath] => do
        let .ok [.expression [.symbol "result", tree, .symbol "nil"]] :=
            Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource (← IO.FS.readFile packetPath)
          | throw (IO.userError "expected one explicitly selected whole-input parser result")
        match Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering.lower
            (← IO.FS.readFile sourcePath) tree with
        | .ok program => pure program
        | .error reason => throw (IO.userError reason)
    | _ => throw (IO.userError "expected optional source and selected-packet paths")
  generate directory label program sample.expected
