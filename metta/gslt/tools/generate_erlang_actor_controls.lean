import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangExecutionData
import Mettapedia.Languages.Erlang.ActorControls
import Mettapedia.Languages.Erlang.ActorExamples
import Mettapedia.Languages.Erlang.StandardActorExamples
import Mettapedia.Languages.Erlang.ParallelActorExamples
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
/-! Actual compiled sequential IR under the experimental local actor adapter. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
open Mettapedia.Languages
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL

def encode (pattern : Syntax.Pattern) : String :=
  CettaWire.Term.render (InferenceCettaWire.encodePattern pattern)
def listText (items : List String) : String :=
  items.foldr (fun item tail => "(LCons " ++ item ++ " " ++ tail ++ ")") "LNil"
def main (arguments : List String) : IO Unit := do
  let (directory, name, portable) ← match arguments with
    | [directory, name] => pure (directory, name, false)
    | [directory, name, "portable"] => pure (directory, name, true)
    | _ => throw (IO.userError "expected directory, case and optional portable profile")
  let (program, expected, mailbox, count) ← match name with
    | "self" => pure (Erlang.ActorControls.selfProgram,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList [.pid 0]) ++ ")", ([] : List Erlang.Value), 4)
    | "empty-peek" => pure (Erlang.ActorControls.emptyPeekProgram,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList
          [.literal (.atom "false"), .literal (.atom "undefined")]) ++ ")", [], 4)
    | "spawn" => pure (Erlang.ActorControls.spawnProgram,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList [.pid 1]) ++ ")", [], 4)
    | "selective" => pure (Erlang.ActorControls.receiveProgram,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList [.literal (.atom "a")]) ++ ")",
        [.literal (.atom "b"), .literal (.atom "a"), .literal (.atom "b")], 16)
    | "blocked" => pure (Erlang.ActorControls.receiveProgram, "ErActorBlocked", [.literal (.atom "b")], 16)
    | "spawn-send" => pure (Erlang.ActorExamples.spawnSend,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList [.literal (.integer 42)]) ++ ")", [], 20)
    | "self-selective" => pure (Erlang.ActorExamples.selfSelective,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList
          [.tuple [.literal (.atom "a"), .literal (.atom "b")]]) ++ ")", [], 30)
    | "ping-pong" => pure (Erlang.StandardActorExamples.pingPong 2,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList [.literal (.atom "done")]) ++ ")", [], 80)
    | "counter" => pure (Erlang.StandardActorExamples.counter,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList [.literal (.integer 2)]) ++ ")", [], 80)
    | "parallel-map" => pure (Erlang.ParallelActorExamples.parallelMap 2 3,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList
          [.cons (.literal (.integer 4)) (.cons (.literal (.integer 6)) (.literal .nil))]) ++ ")", [], 20)
    | "parallel-map-duplicates" => pure (Erlang.ParallelActorExamples.parallelMap 2 2,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList
          [.cons (.literal (.integer 4)) (.cons (.literal (.integer 4)) (.literal .nil))]) ++ ")", [], 20)
    | "causal-forward" => pure (Erlang.ParallelActorExamples.twoSenders,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList
          [.tuple [.literal (.atom "a"), .literal (.atom "b")]]) ++ ")", [], 30)
    | "causal-reverse" => pure (Erlang.ParallelActorExamples.twoSenders,
        "(ErActorValue " ++ encode (ErlangCompilation.valueList
          [.tuple [.literal (.atom "b"), .literal (.atom "a")]]) ++ ")", [], 16)
    | _ => throw (IO.userError "unknown actor case")
  let .ok prepared := ErlangCompilation.prepare program | throw (IO.userError "actor program refused")
  let .ok emitted := ErlangCompilation.ExecutionData.emitText? prepared "er-actors"
    | throw (IO.userError "actor emission refused")
  let box := ErlangMailbox.mailbox ErlangCompilation.value (⟨[], mailbox, []⟩ : Erlang.Mailbox Erlang.Value)
  let locals := ["(ErExecute 0 200 2)", "(ErExecute 1 200 2)", "(ErExecute 2 200 2)"]
  let choices := if ["parallel-map", "parallel-map-duplicates"].contains name then
    (List.replicate 16 locals).flatten ++ ["(ErDeliver 1)", "(ErDeliver 0)"] ++
      (List.replicate count locals).flatten
    else if name = "causal-reverse" then
      (List.replicate 16 locals).flatten ++ ["(ErDeliver 1)"] ++
      (List.replicate 12 locals).flatten ++ ["(ErDeliver 1)", "(ErDeliver 0)"] ++
      (List.replicate count locals).flatten
    else if name = "causal-forward" then
      (List.replicate count (locals ++ ["(ErDeliver 0)"])).flatten
    else if ["spawn-send", "self-selective", "ping-pong", "counter"].contains name then
    (List.replicate count ["(ErExecute 0 200 2)", "(ErExecute 1 200 2)", "(ErDeliver 0)"]).flatten
    else List.replicate count "(ErExecute 0 200 2)" ++
      (if name = "spawn" then ["(ErExecute 1 200 2)", "(ErExecute 1 200 2)"] else [])
  let referenceResult := match name with
    | "self" => Erlang.ActorControls.selfResult
    | "empty-peek" => Erlang.ActorControls.emptyPeekResult
    | "spawn" => Erlang.ActorControls.spawnResult
    | "selective" => Erlang.ActorControls.receiveResult
    | "spawn-send" => Erlang.ActorExamples.spawnSendResult
    | "self-selective" => Erlang.ActorExamples.selfSelectiveResult
    | "ping-pong" => Erlang.StandardActorExamples.pingPongResult
    | "counter" => Erlang.StandardActorExamples.counterResult
    | "parallel-map" => Erlang.ParallelActorExamples.parallelMapReverseResult
    | "parallel-map-duplicates" => Erlang.ParallelActorExamples.duplicateMapReverseResult
    | "causal-forward" => Erlang.ParallelActorExamples.causalForwardResult
    | "causal-reverse" => Erlang.ParallelActorExamples.causalReverseResult
    | _ => Erlang.ActorControls.waitingResult
  let .ok reference := referenceResult | throw (IO.userError "reference actor failed")
  let some root := reference.process? 0 | throw (IO.userError "reference root missing")
  let expectedBox := encode (ErlangMailbox.mailbox ErlangCompilation.value root.mailbox)
  let expectedNetwork := listText (reference.network.map fun message =>
    "(ErEnvelope " ++ toString message.key.sender ++ " " ++ toString message.key.receiver ++
      " " ++ encode (ErlangCompilation.value message.payload) ++ ")")
  let networkCheck := "(if (== $fresh " ++ toString reference.nextPid ++ ")" ++
    " (== $network (quote " ++ expectedNetwork ++ ")) False)"
  let childChecks := reference.processes.filterMap fun process =>
    if process.identity = 0 then none else match process.machine with
      | .halted (.ok values) =>
          let suffix := toString process.identity
          some ("(case (gslt:er-actor:get " ++ suffix ++ " $processes)" ++
            " (((Some (ErLocal $child" ++ suffix ++ " $box" ++ suffix ++
            " (ErMachine ErComplete $cp" ++ suffix ++ " $cs" ++ suffix ++
            " (ClassMachine $ct" ++ suffix ++ " (PApp \"ErDone\" (LCons $cv" ++ suffix ++
            " LNil)) $cq" ++ suffix ++ " $trail" ++ suffix ++ " $cr" ++ suffix ++
            ") $ce" ++ suffix ++ "))) (== $cv" ++ suffix ++ " (quote " ++
            encode (ErlangCompilation.valueList values) ++ "))) ($bad" ++ suffix ++ " False)))")
      | _ => none
  let childCheck := childChecks.foldr (fun check rest => "(if " ++ check ++ " " ++ rest ++ " False)") networkCheck
  let controls :=
    "!(println! (ErlangActorStart " ++ reprStr name ++ "))\n" ++
    "!(let* (($vm (er-actors:begin)) ($mailbox (quote " ++ encode box ++ "))" ++
    " ($initial (ErActorSystem (LCons (ErLocal 0 $mailbox $vm) LNil) LNil 1 LNil))" ++
    " ($direct (gslt:er-actor:choices " ++ listText choices ++ " $initial))" ++
    " ($prefix (gslt:er-actor:choices " ++ listText (choices.take 1) ++ " $initial))" ++
    " ($resumed (gslt:er-actor:choices " ++ listText (choices.drop 1) ++ " $prefix))" ++
    " ($observed (gslt:er-actor:observe $direct)))" ++
    " (case $direct (((ErActorSystem $processes $network $fresh $history)" ++
    " (case (gslt:er-actor:get 0 $processes) (((Some (ErLocal $pid $actualBox $machine))" ++
    " (println! (ErlangActorControl " ++ reprStr name ++ " (== $observed (quote " ++ expected ++ "))" ++
    " (== $direct $resumed) (== $actualBox (quote " ++ expectedBox ++ ")) " ++ childCheck ++
    " $observed)))))))))\n"
  IO.FS.createDirAll directory
  IO.FS.writeFile (System.FilePath.mk directory / "machine.metta") emitted
  IO.FS.writeFile (System.FilePath.mk directory / "controls.metta")
    (if portable then controls.replace "gslt:er-actor:choices " "gslt:er-actor:choices-portable " else controls)
  IO.println s!"emitted actor {name}"
