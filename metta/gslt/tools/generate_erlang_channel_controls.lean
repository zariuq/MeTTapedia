import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannelControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannelExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

/-! Emit the authored point-to-point channel component through the shared
compiler. The OSLF questions and expected results use the same operational
IR; the list/network model supplies their expected queues. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def leafReader : String := "(: er-channel-test:leaves (-> Atom Atom %Undefined%))\n" ++
  "(= (er-channel-test:leaves $plan $nodes) (case $nodes ((LNil LNil)" ++
  " ((LCons (ExploreNode $state $history $states $born $run $consumed) $rest)" ++
  " (let* (($tail (er-channel-test:leaves $plan $rest))" ++
  " ($status (gslt:search:status ClassSearch $plan $run))" ++
  " ($published (gslt:search:publication ClassSearch $run)))" ++
  " (case $status ((SearchComplete (case $published ((LNil (LCons $state $tail)) ($nonempty $tail))))" ++
  " ($pending $tail))))))))\n"

def manifest : Lean.Json := Lean.Json.mkObj [
  ("component", .str "Erlang ordered point-to-point channels"),
  ("questions", .arr (ErlangChannel.Controls.verdicts.map fun entry => Lean.Json.mkObj
    [("name", .str entry.1), ("expectedReachable", Lean.toJson entry.2.1),
     ("wrongReachable", Lean.toJson entry.2.2)]).toArray),
  ("emptyChannelHasStep", Lean.toJson ErlangChannel.Controls.noDelivery),
  ("fifoViolationReachable", Lean.toJson ErlangChannel.Controls.fifoViolation),
  ("zeroBudget", Lean.toJson ErlangChannel.Controls.exhausted),
  ("networkSelectorSoundAndComplete", .str "Erlang.Network.delivers_iff_index"),
  ("sourceSendCoverage", .str "ErlangChannel.Execution.network_send"),
  ("sourceDeliveryCoverage", .str "ErlangChannel.Execution.network_delivery"),
  ("deliveryNoInvention", .str "ErlangChannel.Execution.reference_delivery_iff"),
  ("completeActorScheduler", .bool false),
  ("sequentialCoreErlangExecution", .bool false),
  ("sourceLoweringQualified", .bool false),
  ("fullE0Qualified", .bool false)]

def generate (directory : String) : IO Unit := do
  let spec : CompleteEmission.Spec := ⟨ErlangChannel.plan, [], .base "ErChannelConfig", .canonical⟩
  let .ok emitted := CompleteEmission.emitText? spec "er-channel" .classes
    | throw (IO.userError "channel compiler admission failed")
  let encode := fun pattern => CettaWire.Term.render (InferenceCettaWire.encodePattern pattern)
  let plan := CettaWire.Term.render (CompletePlanWire.planTerm ErlangChannel.plan [] [] (.base "ErChannelConfig"))
  let standard := CettaWire.Term.render
    (StandardWire.commitTerm ErlangChannel.plan .canonical (CompleteEmission.table spec))
  let mut controls := leafReader ++ "(: er-channel-test:plan (-> %Undefined%))\n" ++
    "(= (er-channel-test:plan) (quote " ++ plan ++ "))\n" ++
    "(: er-channel-test:standard (-> %Undefined%))\n" ++
    "(= (er-channel-test:standard) (quote " ++ standard ++ "))\n"
  for sample in ErlangChannel.Controls.examples do
    controls := controls ++
      "!(let* (($plan (er-channel-test:plan)) ($standard (er-channel-test:standard))" ++
      " ($source (quote " ++ encode sample.source ++ ")) ($expected (quote " ++ encode sample.expected ++ "))" ++
      " ($begun (er-channel:begin $source))" ++
      " ($direct (gslt:runner:advance ClassSearch $plan $standard 2000 50 $begun))" ++
      " ($first (gslt:runner:advance ClassSearch $plan $standard 7 50 $begun))" ++
      " ($resumed (gslt:runner:advance ClassSearch $plan $standard 1993 50 $first))" ++
      " ($graphBegin (gslt:explore:begin ClassSearch $plan $standard $source))" ++
      " ($graph (gslt:explore:rounds ClassSearch $plan $standard 6000 $graphBegin))" ++
      " ($graphFirst (gslt:explore:rounds ClassSearch $plan $standard 7 $graphBegin))" ++
      " ($graphResumed (gslt:explore:rounds ClassSearch $plan $standard 5993 $graphFirst)))" ++
      " (case $direct (((ClassMachine $phase $state $search $states $receipts)" ++
      " (case $graph (((Explorer $round $nodes)" ++
      " (let $leaves (er-channel-test:leaves $plan $nodes)" ++
      " (println! (ErlangChannelControl " ++ reprStr sample.name ++
      " (== $phase ClassDone) (== $state $expected) (== $direct $resumed)" ++
      " (== $leaves (LCons $expected LNil)) (gslt:explore:settled ClassSearch $plan $nodes)" ++
      " (== $graph $graphResumed)))))))))))\n"
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") controls
  IO.FS.writeFile (output / "oslf.json") manifest.pretty
  IO.println s!"emitted {ErlangChannel.Controls.examples.length} channel controls"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [directory] => generate directory
  | _ => throw (IO.userError "expected an output directory")
