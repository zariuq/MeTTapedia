import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelEmission

/-! A native rho state-token boundary around the actual authored mailbox
language. Expected mailbox contents come from the independent list model.
This qualifies a component canary, not the complete emitted actor scheduler. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  let spec := ErlangMailboxKernelSource.spec
  let .ok emitted := CompleteEmission.emitText? spec ErlangMailboxKernelSource.name .classes
    | throw (IO.userError "mailbox emission refused")
  let some kernel := ErlangMailboxKernelEmission.render?
    | throw (IO.userError "mailbox entry program did not render")
  let before : Mettapedia.Languages.Erlang.Mailbox String := ⟨["b"], ["a", "b"], []⟩
  let some after := before.remove? | throw (IO.userError "reference remove failed")
  let encode := fun pattern => CettaWire.Term.render (InferenceCettaWire.encodePattern pattern)
  let source := encode (ErlangMailbox.mailbox ErlangMailbox.atom before)
  let expected := encode (ErlangMailbox.node "ErRemoved" [ErlangMailbox.mailbox ErlangMailbox.atom after])
  let controls := "!(import! &self rhometta)\n" ++
    "!(let* (($mailbox (quote " ++ source ++ ")) ($expected (quote " ++ expected ++ "))" ++
    " ($stateChannel (rho:quote (rho:val mailbox-state)))" ++
    " ($process (gslt:er-rho:mailbox-request $stateChannel \"ErRemove\" $mailbox))" ++
    " ($direct (rhometta:run $process)) ($prefix (rhometta:transitions $process))" ++
    " ($tasks (rhometta:values $prefix)))" ++
    " (case $tasks ((($task) (let* (($done (gslt:er-rho:complete-task $task))" ++
    " ($values (rhometta:values $done)))" ++
    " (case $values ((((ErRhoMailboxResult \"ErRemove\" (ErRhoKernelDone $target $account)))" ++
    " (case $account (((ClassMachine $phase $state $query $states $receipts)" ++
    " (println! (ErlangRhoMailboxControl (== $target $expected) (== $phase ClassDone)" ++
    " (== $direct $prefix) (if (== $tasks (quote ())) False True))))))))))))))\n"
  IO.FS.createDirAll directory
  let output := System.FilePath.mk directory
  IO.FS.writeFile (output / "machine.metta") (emitted ++ "\n" ++ kernel)
  IO.FS.writeFile (output / "controls.metta") controls
  IO.println "emitted authored-mailbox rho canary"
