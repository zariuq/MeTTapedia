import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangPrimitiveControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilationControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangExecutionData

/-! Execute prepared arena programs through their actual compiled GSLT step
rules and retained service epochs. Expected results come from the independent
reference model. Native Erlang comparisons are in the sequential gate. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages

open ErlangPrimitiveControls

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [directory, "manifest"] =>
      IO.FS.createDirAll directory
      IO.FS.writeFile (System.FilePath.mk directory / "programs.json")
        (Lean.toJson (Erlang.SequentialExamples.examples.map (·.name))).pretty
      IO.println s!"listed {Erlang.SequentialExamples.examples.length} programs"
  | [directory, "primitives"] =>
      IO.FS.createDirAll directory
      IO.FS.writeFile (System.FilePath.mk directory / "controls.metta") primitiveControls
      IO.println s!"emitted {primitiveCases.length} primitive controls"
  | [directory, label] =>
      let some sample := Erlang.SequentialExamples.examples.find? (·.name == label)
        | throw (IO.userError "unknown sequential case")
      let .ok prepared := ErlangCompilation.prepare sample.program
        | throw (IO.userError "Erlang program preparation refused")
      let .ok emitted := ErlangCompilation.ExecutionData.emitText? prepared "er-example"
        | throw (IO.userError "Erlang machine emission refused")
      let expected := match sample.expected with
        | .ok values => ErlangCompilation.node "ErDone" [ErlangCompilation.valueList values]
        | .error fault => ErlangCompilation.node "ErFault" [ErlangCompilation.fault fault]
      let controls :=
        "!(let* (($begun (er-example:begin)) ($direct (gslt:er:advance 15000 50 $begun))" ++
        " ($first (gslt:er:advance 17 50 $begun)) ($resumed (gslt:er:advance 14983 50 $first))" ++
        " ($expected (quote " ++ encode expected ++ ")))" ++
        " (case $direct (((ErMachine $phase $plan $standard (ClassMachine $status $state $query $states $receipts) $epochs)" ++
        " (println! (ErlangKernelControl " ++ reprStr label ++
        " (== $phase ErComplete) (== $state $expected) (== $direct $resumed)))))))\n"
      IO.FS.createDirAll directory
      let output := System.FilePath.mk directory
      IO.FS.writeFile (output / "machine.metta") emitted
      IO.FS.writeFile (output / "controls.metta") controls
      IO.FS.writeFile (output / "preparation.json") (Lean.Json.mkObj [
        ("name", .str label), ("codeNodes", Lean.toJson sample.program.code.size),
        ("rules", Lean.toJson prepared.compiled.rewrites.length),
        ("sourceLoweringQualified", .bool false), ("fullE0Qualified", .bool false)]).pretty
      IO.println s!"emitted {label}"
  | _ => throw (IO.userError "expected output-directory and primitives|case-name")
