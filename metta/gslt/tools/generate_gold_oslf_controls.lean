import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLFControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLFCollectionControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeOSLFControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

/-! The same mailbox requests are checked at the certified OSLF front door
and executed through the shared MeTTa runner/explorer. This finite comparison
does not prove complete Core Erlang or compiler adequacy. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def leafReader : String := "(: er-test:leaves (-> Atom Atom %Undefined%))\n" ++
  "(= (er-test:leaves $plan $nodes) (case $nodes ((LNil LNil)" ++
  " ((LCons (ExploreNode $state $history $states $born $run $consumed) $rest)" ++
  " (let* (($tail (er-test:leaves $plan $rest))" ++
  " ($status (gslt:search:status ClassSearch $plan $run))" ++
  " ($published (gslt:search:publication ClassSearch $run)))" ++
  " (case $status ((SearchComplete (case $published ((LNil (LCons $state $tail)) ($nonempty $tail))))" ++
  " ($pending $tail))))))))\n"

def manifest : Lean.Json :=
  let row := fun (entry : String × Option Bool × Option Bool) => Lean.Json.mkObj
    [("name", .str entry.1), ("expectedReachable", Lean.toJson entry.2.1),
     ("wrongReachable", Lean.toJson entry.2.2)]
  let conditional := fun (entry : String × Option Bool × Bool) => Lean.Json.mkObj
    [("name", .str entry.1), ("answer", Lean.toJson entry.2.1), ("expected", .bool entry.2.2)]
  let collectionQuestions :=
    (GoldOSLF.CollectionControls.chrVerdicts.zip [true, false, false] ++
     GoldOSLF.CollectionControls.datalogVerdicts.zip [true, true, false]).map fun (entry, expected) =>
      Lean.Json.mkObj [("name", .str entry.1), ("answer", Lean.toJson entry.2),
        ("intended", .bool expected), ("requiredReading", .str "certified collection equality and step coherence")]
  Lean.Json.mkObj [
    ("ocamlPreparedStructural", .arr (GoldOSLF.Controls.structuralVerdicts.map row).toArray),
    ("erlangMailbox", .arr (ErlangMailbox.Controls.verdicts.map row).toArray),
    ("snapshotAndWaiting", .arr ((GoldOSLF.Controls.primitiveVerdicts ++
      ErlangMailbox.Controls.waitingVerdicts).map conditional).toArray),
    ("collectionQuestions", .arr collectionQuestions.toArray),
    ("maudeQuestions", .arr #[
      conditional ("maude-coffee", MaudeCompilation.OSLFControls.coffee, true),
      conditional ("maude-apple", MaudeCompilation.OSLFControls.apple, true),
      conditional ("maude-empty-coffee", MaudeCompilation.OSLFControls.emptyCoffee, false),
      conditional ("maude-initialization", MaudeCompilation.OSLFControls.mutexAfterInitialization, true)]),
    ("exhaustedMailboxQuestion", Lean.toJson ErlangMailbox.Controls.exhaustedVerdict),
    ("fullLanguageAdequacy", .bool false)]

def generate (directory : String) : IO Unit := do
  let spec : CompleteEmission.Spec := ⟨ErlangMailbox.plan, [], .base "ErMailboxConfig", .canonical⟩
  let .ok emitted := CompleteEmission.emitText? spec "er-mailbox" .classes
    | throw (IO.userError "mailbox compiler admission failed")
  let encode := fun pattern => CettaWire.Term.render (InferenceCettaWire.encodePattern pattern)
  let plan := CettaWire.Term.render (CompletePlanWire.planTerm ErlangMailbox.plan [] [] (.base "ErMailboxConfig"))
  let standard := CettaWire.Term.render
    (StandardWire.commitTerm ErlangMailbox.plan .canonical (CompleteEmission.table spec))
  let mut controls := leafReader ++ "(: er-test:plan (-> %Undefined%))\n(= (er-test:plan) (quote " ++ plan ++ "))\n" ++
    "(: er-test:standard (-> %Undefined%))\n(= (er-test:standard) (quote " ++ standard ++ "))\n"
  for sample in ErlangMailbox.Controls.examples do
    controls := controls ++
      "!(let* (($plan (er-test:plan)) ($standard (er-test:standard))" ++
      " ($source (quote " ++ encode sample.source ++ ")) ($expected (quote " ++ encode sample.expected ++ "))" ++
      " ($begun (er-mailbox:begin $source))" ++
      " ($direct (gslt:runner:advance ClassSearch $plan $standard 1000 50 $begun))" ++
      " ($first (gslt:runner:advance ClassSearch $plan $standard 7 50 $begun))" ++
      " ($resumed (gslt:runner:advance ClassSearch $plan $standard 993 50 $first))" ++
      " ($graphBegin (gslt:explore:begin ClassSearch $plan $standard $source))" ++
      " ($graph (gslt:explore:rounds ClassSearch $plan $standard 4000 $graphBegin))" ++
      " ($graphFirst (gslt:explore:rounds ClassSearch $plan $standard 7 $graphBegin))" ++
      " ($graphResumed (gslt:explore:rounds ClassSearch $plan $standard 3993 $graphFirst)))" ++
      " (case $direct (((ClassMachine $phase $state $search $states $receipts)" ++
      " (case $graph (((Explorer $round $nodes)" ++
      " (let $leaves (er-test:leaves $plan $nodes)" ++
      " (println! (GoldOSLFNativeControl " ++ reprStr sample.name ++
      " (== $phase ClassDone) (== $state $expected) (== $direct $resumed)" ++
      " (== $leaves (LCons $expected LNil)) (gslt:explore:settled ClassSearch $plan $nodes)" ++
      " (== $graph $graphResumed)))))))))))\n"
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") controls
  IO.FS.writeFile (output / "oslf.json") manifest.pretty
  IO.println s!"emitted {ErlangMailbox.Controls.examples.length} mailbox controls"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [directory] => generate directory
  | _ => throw (IO.userError "expected an output directory")
