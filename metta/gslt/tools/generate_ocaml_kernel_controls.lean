import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlExecutionData
import Mettapedia.Languages.OCaml.Examples

/-! Structural indexed OCaml machine programs emitted through the existing
shared compiler and runner. Expected terminal data are independent fixtures.
Primitive services, mismatch control and ordinary-source lowering are not
qualified by these component controls. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def leafReader : String := "(: ml-test:leaves (-> Atom Atom %Undefined%))\n" ++
  "(= (ml-test:leaves $plan $nodes) (case $nodes ((LNil LNil)" ++
  " ((LCons (ExploreNode $state $history $states $born $run $consumed) $rest)" ++
  " (let* (($tail (ml-test:leaves $plan $rest))" ++
  " ($status (gslt:search:status ClassSearch $plan $run))" ++
  " ($published (gslt:search:publication ClassSearch $run)))" ++
  " (case $status ((SearchComplete (case $published ((LNil (LCons $state $tail)) ($nonempty $tail))))" ++
  " ($pending $tail))))))))\n"

def generate (directory label : String) : IO Unit := do
  let some sample := OCaml.Examples.structuralExamples.find? (fun sample => sample.name == label)
    | throw (IO.userError "unknown structural OCaml example")
  let .ok prepared := prepare sample.program | throw (IO.userError "OCaml preparation refused")
  let compiled := ExecutionData.spec prepared
  let .ok emitted := CompleteEmission.emitText? compiled "ml-prepared" .classes
    | throw (IO.userError s!"OCaml machine emission refused: {reprStr (plan prepared).obligations}")
  let .ok expected := sample.expected | throw (IO.userError "expected a data result")
  let encode := fun pattern => CettaWire.Term.render (InferenceCettaWire.encodePattern pattern)
  let source := encode (initial sample.program)
  let expected := encode (node "MlDone" [value expected])
  let planWire := CettaWire.Term.render (CompletePlanWire.planTerm (plan prepared) [] [] (.base "MlConfig"))
  let standard := CettaWire.Term.render (StandardWire.commitTerm (plan prepared) .canonical (CompleteEmission.table compiled))
  let controls :=
    "!(let* (($plan (quote " ++ planWire ++ ")) ($standard (quote " ++ standard ++ "))" ++
    " ($source (quote " ++ source ++ ")) ($expected (quote " ++ expected ++ "))" ++
    " ($begun (ml-prepared:begin $source))" ++
    " ($direct (gslt:runner:advance ClassSearch $plan $standard 1000 50 $begun))" ++
    " ($first (gslt:runner:advance ClassSearch $plan $standard 17 50 $begun))" ++
    " ($resumed (gslt:runner:advance ClassSearch $plan $standard 983 50 $first))" ++
    " ($graphBegin (gslt:explore:begin ClassSearch $plan $standard $source))" ++
    " ($graph (gslt:explore:rounds ClassSearch $plan $standard 20000 $graphBegin))" ++
    " ($graphFirst (gslt:explore:rounds ClassSearch $plan $standard 17 $graphBegin))" ++
    " ($graphResumed (gslt:explore:rounds ClassSearch $plan $standard 19983 $graphFirst)))" ++
    " (case $direct (((ClassMachine $phase $state $search $states $receipts)" ++
    " (case $graph (((Explorer $round $nodes)" ++
    " (let $leaves (ml-test:leaves $plan $nodes)" ++
    " (println! (OCamlKernelControl " ++ reprStr label ++
    " (== $phase ClassDone) (== $state $expected) (== $direct $resumed)" ++
    " (== $leaves (LCons $expected LNil)) (gslt:explore:settled ClassSearch $plan $nodes)" ++
    " (== $graph $graphResumed)" ++
    " (gslt:automata:length $states) (gslt:automata:length $receipts)))))))))))\n"
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") (leafReader ++ controls)
  IO.FS.writeFile (output / "preparation.json")
    (Lean.Json.mkObj [("program", .str label), ("codeNodes", Lean.toJson sample.program.code.size),
      ("patterns", Lean.toJson prepared.patternPool.length),
      ("compiledRules", Lean.toJson prepared.compiled.rewrites.length),
      ("scope", .str "Prepared structural IR; native primitive and mismatch services and source lowering remain open")]).pretty
  IO.println s!"prepared {label}: {sample.program.code.size} code nodes"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [directory] => for sample in OCaml.Examples.structuralExamples do
      generate ((System.FilePath.mk directory) / sample.name).toString sample.name
  | [directory, label] => generate directory label
  | _ => throw (IO.userError "expected an output directory and optional structural example name")
