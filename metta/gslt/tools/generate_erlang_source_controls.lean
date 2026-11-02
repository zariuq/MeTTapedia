import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangExecutionData
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! Ordinary textual Core entries through the existing emitted actor runtime.
The source/model gate checks the complete standard corpus separately. These
native controls check blocked waiting and selective receive with resumption.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa

def encode (pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : String :=
  CettaWire.Term.render (InferenceCettaWire.encodePattern pattern)

def listText (items : List String) : String :=
  items.foldr (fun first rest => "(LCons " ++ first ++ " " ++ rest ++ ")") "LNil"

def main (arguments : List String) : IO Unit := do
  let directory :: sourcePath :: packetPath :: label :: profileArguments := arguments
    | throw (IO.userError "expected output, source, selected packet, case and optional profile")
  let profile ← match profileArguments with
    | [] => pure "rho"
    | ["portable"] => pure "portable"
    | ["compare"] => pure "compare"
    | _ => throw (IO.userError "expected portable or compare execution profile")
  let runner := if profile == "portable" then "gslt:er-actor:choices-portable" else "gslt:er-actor:choices"
  let control := if profile == "portable" then "ErlangSourcePortableControl" else "ErlangSourceNativeControl"
  let .ok [.expression [.symbol "result", tree, .symbol "nil"]] :=
      SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "expected one explicitly selected whole-input result")
  let compiled ← match ErlangSourceLowering.lower (← IO.FS.readFile sourcePath) tree with
    | .ok compiled => pure compiled
    | .error reason => throw (IO.userError reason)
  let prepared ← match ErlangCompilation.prepare compiled.program with
    | .ok prepared => pure prepared
    | .error reason => throw (IO.userError reason)
  let emitted ← match ErlangCompilation.ExecutionData.emitText? prepared "er-source" with
    | .ok emitted => pure emitted
    | .error reason => throw (IO.userError reason)
  let empty := encode (ErlangMailbox.mailbox ErlangCompilation.value
    ({} : Mettapedia.Languages.Erlang.Mailbox Mettapedia.Languages.Erlang.Value))
  let expected ← match label with
    | "core_blocked" => pure "ErActorBlocked"
    | "core_selective" => pure ("(ErActorValue " ++ encode (ErlangCompilation.valueList
        [.tuple [.literal (.atom "a"), .literal (.atom "b")]]) ++ ")")
    | "core_function_message" => pure ("(ErActorValue " ++ encode (ErlangCompilation.valueList
        [.literal (.integer 42)]) ++ ")")
    | _ => throw (IO.userError "unknown independent actor observation fixture")
  let choices := (List.replicate 30 ["(ErExecute 0 200 2)", "(ErDeliver 0)"]).flatten
  let controls :=
    "!(println! (ErlangSourceStart " ++ reprStr label ++ "))\n" ++
    "!(let* (($vm (er-source:begin)) ($box (quote " ++ empty ++ "))" ++
    " ($initial (ErActorSystem (LCons (ErLocal 0 $box $vm) LNil) LNil 1 LNil))" ++
    " ($direct (" ++ runner ++ " " ++ listText choices ++ " $initial))" ++
    " ($first (" ++ runner ++ " " ++ listText (choices.take 1) ++ " $initial))" ++
    " ($resumed (" ++ runner ++ " " ++ listText (choices.drop 1) ++ " $first)))" ++
    " (case $direct (((ErActorSystem $processes $network $fresh $history)" ++
    " (case (gslt:er-actor:get 0 $processes) (((Some (ErLocal $pid $actualBox $machine))" ++
    " (println! (" ++ control ++ " " ++ reprStr label ++
    " (== (gslt:er-actor:observe $direct) (quote " ++ expected ++ "))" ++
    " (== $direct $resumed) (== $actualBox $box)" ++
    " (if (== $fresh 1) (== $network LNil) False)" ++
    (if profile == "compare" then
      " (== $direct (gslt:er-actor:choices-portable " ++ listText choices ++ " $initial))" else "") ++
    ")))))))))\n"
  match SpaceSemantics.readProgram controls with
  | .ok parsed =>
      unless parsed.initializers.length == 2 do
        throw (IO.userError "generated native commands were not retained")
  | .error reason => throw (IO.userError ("generated native controls are malformed: " ++ reason))
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") controls
  IO.println s!"emitted source {label}: {compiled.program.code.size} instructions"
