import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRExecutionData
import Mettapedia.Languages.CHR.Examples

/-! Whole prepared-IR CHR controls. The expected final constraints are
independent program fixtures, also checked in SWI. Ordinary source reading
and the source/controller correspondence remain separate contracts. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.Languages.CHR
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat CHRCompilation
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def generate (directory label : String) : IO Unit := do
  let some sample := Examples.examples.find? (fun sample => sample.name == label)
    | throw (IO.userError "unknown CHR reference example")
  let .ok prepared := prepare sample.program sample.inputs
    | throw (IO.userError s!"CHR preparation refused: {reprStr (prepare sample.program sample.inputs)}")
  let .ok emitted := ExecutionData.emitText? prepared sample.inputs "prepared-chr"
    | throw (IO.userError s!"CHR emission refused: {reprStr (ExecutionData.emitText? prepared sample.inputs "prepared-chr")}")
  let some expected := sample.expected.mapM (constraint? prepared.vocabulary)
    | throw (IO.userError "expected observation cannot be encoded")
  let spec := ExecutionData.spec prepared
  let observed := Complete.Normalized.commit (plan prepared) .canonical (.collection .hashBag expected none)
  let target := CettaWire.Term.render (InferenceCettaWire.encodePattern observed)
  let names := (encodeList CettaWire.Term.string (CompleteEmission.table spec)).render
  let controls :=
    "!(let* (($begun (prepared-chr:begin))" ++
    " ($direct (gslt:chr:advance 2000 20 $begun))" ++
    " ($first (gslt:chr:advance 25 20 $begun))" ++
    " ($resumed (gslt:chr:advance 1975 20 $first))" ++
    " ($result (gslt:chr:result $direct)))" ++
    " (case $result (((ChrResult $phase $store $history $receipts)" ++
    " (let* (($names (quote " ++ names ++ ")) ($expected (quote " ++ target ++ "))" ++
    " ($actual (gslt:canon:canon $names $store)))" ++
    " (println! (CHRWholeProgramControl " ++ reprStr label ++
    " (== $phase ChrComplete) (== $actual $expected) (== $direct $resumed)" ++
    " (gslt:automata:length $history) (gslt:automata:length $receipts))))))))\n"
  let wireControls := ([0,1,15,16,-7,2^120+7,-(2^120)+7] : List Int).map fun number =>
    let payload := CettaWire.Term.render (InferenceCettaWire.encodePattern (integer number))
    "!(let* (($expected (quote " ++ payload ++ ")) ($actual (gslt:chr:encode-integer " ++ toString number ++ "))" ++
      " ($decoded (gslt:chr:decode-integer $expected)))" ++
      " (println! (CHRWireControl " ++ reprStr (toString number) ++
      " (== $actual $expected) (== $decoded (Some " ++ toString number ++ ")))))\n"
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "query.metta") emitted
  IO.FS.writeFile (output / "controls.metta") (controls ++ String.join wireControls)
  IO.FS.writeFile (output / "preparation.json")
    (Lean.Json.mkObj [("program", .str label), ("sourceRules", Lean.toJson sample.program.rules.length),
      ("compiledOccurrences", Lean.toJson prepared.entries.length),
      ("expectedConstraints", Lean.toJson sample.expected.length),
      ("scope", .str "Prepared IR native controls; source frontend and semantic correspondence remain open")]).pretty
  IO.println s!"prepared {label}: {prepared.entries.length} compiled head occurrences"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | directory :: "--batch" :: labels =>
      if labels.isEmpty then throw (IO.userError "expected example names after --batch")
      for label in labels do
        generate ((System.FilePath.mk directory) / label).toString label
  | [directory, label] => generate directory label
  | _ => throw (IO.userError "expected output directory and example name, or --batch and example names")
